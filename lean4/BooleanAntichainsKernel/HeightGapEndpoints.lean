import BooleanAntichainsKernel.UnorderedFullHeight

namespace BooleanAntichainsKernel

open Finset

variable {L : Type*} [Fintype L] [DecidableEq L]
variable [Lattice L] [OrderBot L] [OrderTop L]

/-- The paper's finite natural-number height, with the `ENat` conversion
guard proved immediately below. -/
noncomputable def latticeHeight (x : L) : ℕ := (Order.height x).toNat

omit [DecidableEq L] [OrderBot L] [OrderTop L] in
lemma coe_latticeHeight (x : L) : (latticeHeight x : ℕ∞) = Order.height x :=
  ENat.coe_toNat (finite_height_lt_top x).ne

omit [DecidableEq L] [OrderBot L] [OrderTop L] in
lemma latticeHeight_strictMono : StrictMono (latticeHeight (L := L)) := by
  intro x y hxy
  apply ENat.coe_lt_coe.mp
  rw [coe_latticeHeight, coe_latticeHeight]
  exact Order.height_strictMono hxy (finite_height_lt_top x)

omit [DecidableEq L] [OrderBot L] [OrderTop L] in
lemma latticeHeight_mono : Monotone (latticeHeight (L := L)) := latticeHeight_strictMono.monotone

/-- The exact nonnegative integer gap displayed in Equation (3.1). -/
noncomputable def reconstructionGap {k : ℕ} (H : Fin k → L) (S : Finset (Fin k)) : ℕ :=
  latticeHeight (meetFace H S) - latticeHeight (joinFace H S)

omit [DecidableEq L] in
lemma reconstructionGap_eq_zero_iff {k : ℕ} (H : Fin k → L) (S : Finset (Fin k)) :
    reconstructionGap H S = 0 ↔
      Order.height (joinFace H S) = Order.height (meetFace H S) := by
  rw [reconstructionGap, Nat.sub_eq_zero_iff_le]
  have hUV := latticeHeight_mono (joinFace_le_meetFace H S)
  constructor
  · intro hVU
    have heq := congrArg (fun n : ℕ ↦ (n : ℕ∞)) (le_antisymm hUV hVU)
    simpa only [coe_latticeHeight] using heq
  · intro heq
    have hnat := congrArg ENat.toNat heq
    exact hnat.ge

omit [DecidableEq L] [OrderBot L] in
lemma natural_atomic_rise_iff {k : ℕ} (H : Fin k → L) (i : Fin k) :
    latticeHeight (commonMeet H) < latticeHeight (reconstructedAtom H i) ↔
      Order.height (commonMeet H) < Order.height (reconstructedAtom H i) := by
  rw [← ENat.coe_lt_coe, coe_latticeHeight, coe_latticeHeight]

omit [DecidableEq L] in
/-- The exact displayed natural-height criterion of Theorem 3.1. -/
theorem literal_height_gap_criterion {k : ℕ} (H : Fin k → L) :
    IsBooleanTuple H ↔
      (∀ i, latticeHeight (commonMeet H) < latticeHeight (reconstructedAtom H i)) ∧
      (∀ S : Finset (Fin k), reconstructionGap H S = 0) := by
  rw [global_height_gap_criterion]
  simp only [ReconstructedAtomsRise, ReconstructionGapsVanish,
    natural_atomic_rise_iff, reconstructionGap_eq_zero_iff]

lemma product_of_indicators {ι : Type*} [Fintype ι] (p : ι → Prop) [DecidablePred p] :
    (∏ i : ι, if p i then 1 else 0 : ℕ) = if ∀ i, p i then 1 else 0 := by
  by_cases hall : ∀ i, p i
  · simp [hall]
  · obtain ⟨i, hi⟩ := not_forall.mp hall
    rw [if_neg hall]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

/-- Both finite products of indicators in the manuscript's exact enumerator. -/
noncomputable def literalCriterionIndicator {k : ℕ} (H : Fin k → L) : ℕ := by
  classical
  exact (∏ i : Fin k,
    if latticeHeight (commonMeet H) < latticeHeight (reconstructedAtom H i) then 1 else 0) *
    ∏ S : Finset (Fin k), if reconstructionGap H S = 0 then 1 else 0

omit [DecidableEq L] in
lemma literalCriterionIndicator_eq {k : ℕ} (H : Fin k → L) :
    literalCriterionIndicator H = globalCriterionIndicator H := by
  classical
  have hp : ((∀ i, latticeHeight (commonMeet H) < latticeHeight (reconstructedAtom H i)) ∧
      ∀ S, reconstructionGap H S = 0) ↔
      ReconstructedAtomsRise H ∧ ReconstructionGapsVanish H :=
    (literal_height_gap_criterion H).symm.trans (global_height_gap_criterion H)
  unfold literalCriterionIndicator globalCriterionIndicator
  simp only [product_of_indicators]
  by_cases ha : ∀ i, latticeHeight (commonMeet H) < latticeHeight (reconstructedAtom H i)
  · by_cases hb : ∀ S : Finset (Fin k), reconstructionGap H S = 0
    · have hold := hp.mp ⟨ha, hb⟩
      rw [if_pos ha, if_pos hb, if_pos hold, mul_one]
    · have hold : ¬ (ReconstructedAtomsRise H ∧ ReconstructionGapsVanish H) :=
        fun h ↦ hb (hp.mpr h).2
      rw [if_pos ha, if_neg hb, if_neg hold, mul_zero]
  · have hold : ¬ (ReconstructedAtomsRise H ∧ ReconstructionGapsVanish H) :=
      fun h ↦ ha (hp.mpr h).1
    rw [if_neg ha, zero_mul, if_neg hold]

theorem literal_height_gap_enumerator (k : ℕ) :
    Fintype.card (BooleanAntichain k L) =
      (∑ H : Fin k → L, literalCriterionIndicator H) / k.factorial := by
  simp_rw [literalCriterionIndicator_eq]
  exact global_height_gap_enumerator

omit [DecidableEq L] [OrderBot L] in
theorem booleanTuple_size_le_height {k : ℕ} {H : Fin k → L} (hH : IsBooleanTuple H) :
    k ≤ latticeHeight (⊤ : L) := by
  have hbounds := (boolean_face_rank_bounds hH latticeHeight latticeHeight_strictMono Finset.univ).1
  simp only [meetFace_univ, Finset.card_univ, Fintype.card_fin] at hbounds
  omega

theorem booleanAntichain_count_above_height (k : ℕ) (hk : latticeHeight (⊤ : L) < k) :
    Fintype.card (BooleanAntichain k L) = 0 := by
  have hempty : IsEmpty (BooleanAntichain k L) := ⟨fun C ↦ by
    let e := canonicalEnumeration C
    have hH := (isBooleanTuple_iff_antichain_of_equiv C.1 e).mpr C.2.2
    exact hk.not_ge (booleanTuple_size_le_height hH)⟩
  exact Fintype.card_eq_zero_iff.mpr hempty

omit [Fintype L] [DecidableEq L] [OrderBot L] in
theorem empty_booleanTuple : IsBooleanTuple (Fin.elim0 : Fin 0 → L) := by
  constructor
  · intro S T _
    exact Subsingleton.elim S T
  · intro S T
    have hS : S = ∅ := Subsingleton.elim _ _
    have hT : T = ∅ := Subsingleton.elim _ _
    simp [hS, hT, meetFace]

theorem booleanAntichain_count_zero : Fintype.card (BooleanAntichain 0 L) = 1 := by
  have hcard : Fintype.card (OrderedBooleanTuple 0 L) = 1 := by
    letI : Unique (OrderedBooleanTuple 0 L) :=
      { default := ⟨Fin.elim0, empty_booleanTuple⟩
        uniq := fun H ↦ Subtype.ext (funext fun i ↦ Fin.elim0 i) }
    exact Fintype.card_unique
  simpa [card_orderedBooleanTuple] using hcard

end BooleanAntichainsKernel
