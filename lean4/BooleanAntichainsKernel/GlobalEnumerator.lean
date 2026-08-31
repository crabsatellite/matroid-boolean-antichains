import BooleanAntichainsKernel.Core
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Unordered Boolean antichains and the global enumerator

This file connects the ordered tuples of the height-gap criterion to the
literal unordered finite-set objects counted in the manuscript.  The
factorial is earned from enumeration equivalences; it is not built into the
definition of the count.
-/

namespace BooleanAntichainsKernel

open Finset

section Unordered

variable {L : Type*} [Fintype L] [DecidableEq L]
variable [Lattice L] [OrderBot L] [OrderTop L]

/-- The literal meet face of an unordered family, indexed by omitted members. -/
def antichainMeetFace (C : Finset L) (S : Finset C) : L :=
  (Finset.univ \ S).inf fun x : C ↦ x.1

/--
The manuscript definition of an unordered Boolean antichain: its power-set
meet map is a lattice anti-isomorphism onto its image.  Complementing the
source power set turns that map into the injective join-preserving map below.
-/
def IsBooleanAntichain (C : Finset L) : Prop :=
  Function.Injective (antichainMeetFace C) ∧
    ∀ S T : Finset C,
      antichainMeetFace C (S ∪ T) =
        antichainMeetFace C S ⊔ antichainMeetFace C T

/-- Size-`k` unordered Boolean antichains in `L`. -/
abbrev BooleanAntichain (k : ℕ) (L : Type*) [DecidableEq L]
    [Lattice L] [OrderBot L] [OrderTop L] :=
  {C : Finset L // C.card = k ∧ IsBooleanAntichain C}

noncomputable instance instFintypeBooleanAntichain {k : ℕ} :
    Fintype (BooleanAntichain k L) := by
  classical
  exact Subtype.fintype _

/-- Ordered Boolean tuples, used only as the labelled cover of the unordered
objects. -/
abbrev OrderedBooleanTuple (k : ℕ) (L : Type*)
    [Lattice L] [OrderBot L] [OrderTop L] :=
  {H : Fin k → L // IsBooleanTuple H}

noncomputable instance instFintypeOrderedBooleanTuple {k : ℕ} :
    Fintype (OrderedBooleanTuple k L) := by
  classical
  exact Subtype.fintype _

omit [Fintype L] [DecidableEq L] [OrderBot L] in
lemma isBooleanTuple_injective {k : ℕ} {H : Fin k → L}
    (hH : IsBooleanTuple H) : Function.Injective H := by
  intro i j hij
  have hfaces : meetFace H (Finset.univ.erase i) =
      meetFace H (Finset.univ.erase j) := by
    rw [meetFace_complement_singleton, meetFace_complement_singleton]
    exact hij
  exact (Finset.erase_inj Finset.univ (Finset.mem_univ i)).mp (hH.1 hfaces)

/-- The finite carrier underlying an ordered tuple. -/
def orderedCarrier {k : ℕ} (H : Fin k → L) : Finset L :=
  Finset.univ.image H

omit [Fintype L] [OrderBot L] in
lemma orderedCarrier_card {k : ℕ} {H : Fin k → L}
    (hH : IsBooleanTuple H) : (orderedCarrier H).card = k := by
  simpa [orderedCarrier] using
    Finset.card_image_of_injective (Finset.univ : Finset (Fin k))
      (isBooleanTuple_injective hH)

/-- The canonical equivalence from tuple positions to the tuple's carrier. -/
noncomputable def indexEquivCarrier {k : ℕ} (H : Fin k → L)
    (hH : Function.Injective H) :
    Fin k ≃ ↥(orderedCarrier H) :=
  Equiv.ofBijective
    (fun i ↦ ⟨H i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩)
    ⟨fun _ _ h ↦ hH (Subtype.ext_iff.mp h), fun x ↦ by
      rcases Finset.mem_image.mp x.2 with ⟨i, _, hi⟩
      exact ⟨i, Subtype.ext hi⟩⟩

omit [Fintype L] [Lattice L] [OrderBot L] [OrderTop L] in
@[simp] lemma indexEquivCarrier_apply {k : ℕ} (H : Fin k → L)
    (hH : Function.Injective H) (i : Fin k) :
    ((indexEquivCarrier H hH i : ↥(orderedCarrier H)) : L) = H i := rfl

omit [Fintype L] [OrderBot L] in
lemma antichainMeetFace_map_equiv {k : ℕ} (C : Finset L)
    (e : Fin k ≃ C) (S : Finset (Fin k)) :
    antichainMeetFace C (e.finsetCongr S) =
      meetFace (fun i ↦ ((e i : C) : L)) S := by
  rw [antichainMeetFace, Equiv.finsetCongr_apply,
    ← Finset.map_univ_equiv e, ← Finset.map_sdiff, Finset.inf_map]
  rfl

omit [Fintype L] [OrderBot L] in
/-- Booleanity is invariant under every enumeration of the carrier. -/
theorem isBooleanTuple_iff_antichain_of_equiv {k : ℕ} (C : Finset L)
    (e : Fin k ≃ C) :
    IsBooleanTuple (fun i ↦ ((e i : C) : L)) ↔ IsBooleanAntichain C := by
  let E : Finset (Fin k) ≃ Finset C := e.finsetCongr
  let H : Fin k → L := fun i ↦ ((e i : C) : L)
  have htransport (S : Finset (Fin k)) :
      antichainMeetFace C (E S) = meetFace H S := by
    exact antichainMeetFace_map_equiv C e S
  have E_union (S T : Finset (Fin k)) : E (S ∪ T) = E S ∪ E T := by
    simp [E, Equiv.finsetCongr_apply, Finset.map_union]
  constructor
  · intro hH
    constructor
    · intro A B hAB
      apply E.symm.injective
      apply hH.1
      calc
        meetFace H (E.symm A) = antichainMeetFace C A := by
          rw [← htransport (E.symm A), E.apply_symm_apply]
        _ = antichainMeetFace C B := hAB
        _ = meetFace H (E.symm B) := by
          rw [← htransport (E.symm B), E.apply_symm_apply]
    · intro A B
      let S := E.symm A
      let T := E.symm B
      calc
        antichainMeetFace C (A ∪ B) =
            antichainMeetFace C (E (S ∪ T)) := by
              congr 1
              rw [E_union, show E S = A by simp [S], show E T = B by simp [T]]
        _ = meetFace H (S ∪ T) := htransport (S ∪ T)
        _ = meetFace H S ⊔ meetFace H T := hH.2 S T
        _ = antichainMeetFace C A ⊔ antichainMeetFace C B := by
              rw [← htransport S, ← htransport T]
              simp [S, T]
  · intro hC
    constructor
    · intro S T hST
      apply E.injective
      apply hC.1
      calc
        antichainMeetFace C (E S) = meetFace H S := htransport S
        _ = meetFace H T := hST
        _ = antichainMeetFace C (E T) := (htransport T).symm
    · intro S T
      rw [← htransport (S ∪ T), ← htransport S, ← htransport T]
      simpa [E, Equiv.finsetCongr_apply, Finset.map_union] using hC.2 (E S) (E T)

omit [Fintype L] [OrderBot L] in
lemma orderedCarrier_isBoolean {k : ℕ} {H : Fin k → L}
    (hH : IsBooleanTuple H) : IsBooleanAntichain (orderedCarrier H) := by
  let e := indexEquivCarrier H (isBooleanTuple_injective hH)
  exact (isBooleanTuple_iff_antichain_of_equiv (orderedCarrier H) e).mp (by simpa [e])

omit [Fintype L] [Lattice L] [OrderBot L] [OrderTop L] in
lemma orderedCarrier_of_equiv {k : ℕ} (C : Finset L) (e : Fin k ≃ C) :
    orderedCarrier (fun i ↦ ((e i : C) : L)) = C := by
  ext x
  constructor
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨i, _, hi⟩
    rw [← hi]
    exact (e i).2
  · intro hx
    obtain ⟨i, hi⟩ := e.surjective ⟨x, hx⟩
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i,
      congrArg Subtype.val hi⟩

/-- The canonical enumeration chosen for a size-`k` carrier. -/
noncomputable def canonicalEnumeration {k : ℕ} (C : BooleanAntichain k L) :
    Fin k ≃ C.1 :=
  (Finset.equivFinOfCardEq C.2.1).symm

omit [Fintype L] in
lemma canonicalIndex_congr {k : ℕ} {C D : BooleanAntichain k L}
    (hCD : C = D) (x : L) (hxC : x ∈ C.1) (hxD : x ∈ D.1) :
    (canonicalEnumeration C).symm ⟨x, hxC⟩ =
      (canonicalEnumeration D).symm ⟨x, hxD⟩ := by
  subst D
  rfl

/-- An unordered Boolean antichain together with the unique permutation that
turns its canonical enumeration into a specified enumeration. -/
abbrev EnumeratedBooleanAntichain (k : ℕ) (L : Type*) [DecidableEq L]
    [Lattice L] [OrderBot L] [OrderTop L] :=
  BooleanAntichain k L × Equiv.Perm (Fin k)

noncomputable instance instFintypeEnumeratedBooleanAntichain {k : ℕ} :
    Fintype (EnumeratedBooleanAntichain k L) := by
  classical
  exact instFintypeProd _ _

noncomputable def enumeratedToOrdered {k : ℕ} :
    EnumeratedBooleanAntichain k L → OrderedBooleanTuple k L := fun x ↦
  let e : Fin k ≃ x.1.1 := x.2.trans (canonicalEnumeration x.1)
  ⟨fun i ↦ ((e i : x.1.1) : L),
    (isBooleanTuple_iff_antichain_of_equiv x.1.1 e).mpr x.1.2.2⟩

/-- The unique permutation that expresses an ordered Boolean tuple relative
to the canonical enumeration of its carrier. -/
noncomputable def tuplePermutation {k : ℕ} (H : OrderedBooleanTuple k L) :
    Equiv.Perm (Fin k) :=
  let C : BooleanAntichain k L :=
    ⟨orderedCarrier H.1, orderedCarrier_card H.2,
      orderedCarrier_isBoolean H.2⟩
  Equiv.ofBijective
    (fun i ↦ (canonicalEnumeration C).symm
      ⟨H.1 i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩)
    ⟨by
      intro i j hij
      apply isBooleanTuple_injective H.2
      exact Subtype.ext_iff.mp ((canonicalEnumeration C).symm.injective hij), by
      intro y
      let x : C.1 := canonicalEnumeration C y
      rcases Finset.mem_image.mp x.2 with ⟨i, _, hi⟩
      refine ⟨i, (canonicalEnumeration C).injective ?_⟩
      rw [Equiv.apply_symm_apply]
      exact Subtype.ext hi⟩

noncomputable def orderedToEnumerated {k : ℕ} :
    OrderedBooleanTuple k L → EnumeratedBooleanAntichain k L := fun H ↦
  let C : BooleanAntichain k L :=
    ⟨orderedCarrier H.1, orderedCarrier_card H.2,
      orderedCarrier_isBoolean H.2⟩
  (C, tuplePermutation H)

/-- The labelled cover is exactly the product of unordered antichains with
the permutations of a canonical enumeration. -/
noncomputable def enumeratedEquivOrdered {k : ℕ} :
    EnumeratedBooleanAntichain k L ≃ OrderedBooleanTuple k L where
  toFun := enumeratedToOrdered
  invFun := orderedToEnumerated
  left_inv := by
    rintro ⟨C, σ⟩
    let e : Fin k ≃ C.1 := σ.trans (canonicalEnumeration C)
    let H : Fin k → L := fun i ↦ ((e i : C.1) : L)
    have hH : IsBooleanTuple H :=
      (isBooleanTuple_iff_antichain_of_equiv C.1 e).mpr C.2.2
    let C' : BooleanAntichain k L :=
      ⟨orderedCarrier H, orderedCarrier_card hH,
        orderedCarrier_isBoolean hH⟩
    have hCeq : C' = C :=
      Subtype.ext (orderedCarrier_of_equiv C.1 e)
    change (C', tuplePermutation ⟨H, hH⟩) = (C, σ)
    apply Prod.ext
    · exact hCeq
    · apply Equiv.ext
      intro i
      have hiC' : H i ∈ C'.1 := by
        change H i ∈ orderedCarrier H
        exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
      have hiC : H i ∈ C.1 := by
        change ((e i : C.1) : L) ∈ C.1
        exact (e i).2
      change (canonicalEnumeration C').symm
          ⟨H i, hiC'⟩ = σ i
      rw [canonicalIndex_congr hCeq (H i) hiC' hiC]
      have hsub : (⟨H i, hiC⟩ : C.1) = e i := Subtype.ext rfl
      rw [hsub]
      simp [e, Equiv.trans_apply]
  right_inv := by
    intro H
    apply Subtype.ext
    funext i
    let C : BooleanAntichain k L :=
      ⟨orderedCarrier H.1, orderedCarrier_card H.2,
        orderedCarrier_isBoolean H.2⟩
    change (((canonicalEnumeration C)
      (tuplePermutation H i) : C.1) : L) = H.1 i
    change (((canonicalEnumeration C)
      ((canonicalEnumeration C).symm
        ⟨H.1 i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩) : C.1) : L) = H.1 i
    rw [Equiv.apply_symm_apply]

theorem card_enumeratedBooleanAntichain {k : ℕ} :
    Fintype.card (EnumeratedBooleanAntichain k L) =
      Fintype.card (BooleanAntichain k L) * k.factorial := by
  classical
  rw [Fintype.card_prod, Fintype.card_perm, Fintype.card_fin]

theorem card_orderedBooleanTuple {k : ℕ} :
    Fintype.card (OrderedBooleanTuple k L) =
      Fintype.card (BooleanAntichain k L) * k.factorial := by
  rw [← card_enumeratedBooleanAntichain]
  exact (Fintype.card_congr enumeratedEquivOrdered).symm

/-- The product of the paper's `0/1` criterion indicators for one tuple. -/
noncomputable def globalCriterionIndicator {k : ℕ} (H : Fin k → L) : ℕ := by
  classical
  exact if ReconstructedAtomsRise H ∧ ReconstructionGapsVanish H then 1 else 0

omit [DecidableEq L] in
theorem sum_globalCriterionIndicator {k : ℕ} :
    (∑ H : Fin k → L, globalCriterionIndicator H) =
      Fintype.card (OrderedBooleanTuple k L) := by
  classical
  rw [Fintype.card_subtype]
  simp_rw [global_height_gap_criterion]
  simp [globalCriterionIndicator]

/--
The exact enumerator in `thm:global-gap`: the number of unordered size-`k`
Boolean antichains is the sum of the literal tuple indicators divided by
`k!`.  The preceding equivalence proves the free `k!` multiplicity.
-/
theorem global_height_gap_enumerator {k : ℕ} :
    Fintype.card (BooleanAntichain k L) =
      (∑ H : Fin k → L, globalCriterionIndicator H) / k.factorial := by
  rw [sum_globalCriterionIndicator, card_orderedBooleanTuple]
  exact (Nat.mul_div_left _ (Nat.factorial_pos k)).symm

end Unordered

end BooleanAntichainsKernel
