import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.SDiff
import Mathlib.Order.KrullDimension

/-!
# Boolean antichains in finite lattices: exact reconstruction data

This file translates the literal objects used in Section 3 of the manuscript.
No theorem below takes a paper result, reference result, certificate, or
unproved semantic adapter as an input.
-/

namespace BooleanAntichainsKernel

open Finset

section FiniteLattice

variable {L : Type*} [Lattice L] [OrderBot L] [OrderTop L]

/-- The paper's common meet `X_H = ∧ i, H_i`. -/
def commonMeet {k : ℕ} (H : Fin k → L) : L :=
  Finset.univ.inf H

/-- The reconstructed atom `A_i(H) = ∧ j ≠ i, H_j`. -/
def reconstructedAtom {k : ℕ} (H : Fin k → L) (i : Fin k) : L :=
  (Finset.univ.erase i).inf H

/-- The meet face `V_H(S) = ∧ j ∉ S, H_j`. -/
def meetFace {k : ℕ} (H : Fin k → L) (S : Finset (Fin k)) : L :=
  (Finset.univ \ S).inf H

/-- The reconstructed join face `U_H(S) = X_H ∨ ∨ i ∈ S, A_i(H)`. -/
def joinFace {k : ℕ} (H : Fin k → L) (S : Finset (Fin k)) : L :=
  commonMeet H ⊔ S.sup (reconstructedAtom H)

/--
An ordered Boolean antichain, expressed through the manuscript's literal
power-set meet map.  `meetFace` is injective and preserves binary joins; it
always preserves binary meets (proved below).  Hence it is precisely the
lattice embedding of `B_k` whose coatoms are the entries of `H`.
-/
def IsBooleanTuple {k : ℕ} (H : Fin k → L) : Prop :=
  Function.Injective (meetFace H) ∧
    ∀ S T : Finset (Fin k),
      meetFace H (S ∪ T) = meetFace H S ⊔ meetFace H T

/-- The exact zero-gap predicate.  In a finite lattice, equality of these
heights is equivalent to the manuscript's natural-number height difference
being zero. -/
def ReconstructionGapsVanish {k : ℕ} (H : Fin k → L) : Prop :=
  ∀ S : Finset (Fin k), Order.height (joinFace H S) = Order.height (meetFace H S)

/-- The exact atomic-rise predicate from `eq:atomic-rise`. -/
def ReconstructedAtomsRise {k : ℕ} (H : Fin k → L) : Prop :=
  ∀ i : Fin k, Order.height (commonMeet H) < Order.height (reconstructedAtom H i)

omit [OrderBot L] in
lemma commonMeet_eq_meetFace_empty {k : ℕ} (H : Fin k → L) :
    commonMeet H = meetFace H ∅ := by
  simp [commonMeet, meetFace]

omit [OrderBot L] in
@[simp] lemma reconstructedAtom_eq_meetFace_singleton {k : ℕ}
    (H : Fin k → L) (i : Fin k) :
    reconstructedAtom H i = meetFace H {i} := by
  simp [reconstructedAtom, meetFace, Finset.sdiff_singleton_eq_erase]

omit [OrderBot L] in
@[simp] lemma meetFace_empty {k : ℕ} (H : Fin k → L) :
    meetFace H ∅ = commonMeet H := by
  exact (commonMeet_eq_meetFace_empty H).symm

omit [OrderBot L] in
@[simp] lemma meetFace_univ {k : ℕ} (H : Fin k → L) :
    meetFace H Finset.univ = ⊤ := by
  simp [meetFace]

omit [OrderBot L] in
@[simp] lemma meetFace_complement_singleton {k : ℕ}
    (H : Fin k → L) (i : Fin k) :
    meetFace H (Finset.univ.erase i) = H i := by
  rw [meetFace, Finset.sdiff_erase_self (Finset.mem_univ i), Finset.inf_singleton]

omit [OrderBot L] in
lemma meetFace_inter {k : ℕ} (H : Fin k → L)
    (S T : Finset (Fin k)) :
    meetFace H (S ∩ T) = meetFace H S ⊓ meetFace H T := by
  simp only [meetFace, Finset.sdiff_inter_distrib_right, Finset.inf_union]

omit [OrderBot L] in
lemma commonMeet_le_reconstructedAtom {k : ℕ} (H : Fin k → L) (i : Fin k) :
    commonMeet H ≤ reconstructedAtom H i := by
  exact Finset.inf_mono (Finset.erase_subset i Finset.univ)

omit [OrderBot L] in
lemma reconstructedAtom_le_meetFace_of_mem {k : ℕ} (H : Fin k → L)
    {S : Finset (Fin k)} {i : Fin k} (hi : i ∈ S) :
    reconstructedAtom H i ≤ meetFace H S := by
  apply Finset.inf_mono
  intro j hj
  rcases Finset.mem_sdiff.mp hj with ⟨_, hjS⟩
  exact Finset.mem_erase.mpr ⟨by
    intro hji
    exact hjS (by simpa [hji] using hi), Finset.mem_univ j⟩

omit [OrderBot L] in
lemma reconstructedAtom_inf_entry {k : ℕ} (H : Fin k → L) (i : Fin k) :
    reconstructedAtom H i ⊓ H i = commonMeet H := by
  rw [reconstructedAtom, commonMeet, inf_comm, ← Finset.inf_insert,
    Finset.insert_erase (Finset.mem_univ i)]

/-- The manuscript's unconditional comparison `U_H(S) ≤ V_H(S)`. -/
lemma joinFace_le_meetFace {k : ℕ} (H : Fin k → L) (S : Finset (Fin k)) :
    joinFace H S ≤ meetFace H S := by
  apply sup_le
  · exact Finset.inf_mono Finset.sdiff_subset
  · exact Finset.sup_le fun i hi ↦ reconstructedAtom_le_meetFace_of_mem H hi

omit [OrderBot L] [OrderTop L] in
lemma finite_height_lt_top [Fintype L] (x : L) : Order.height x < ⊤ := by
  apply lt_top_iff_ne_top.mpr
  intro htop
  obtain ⟨p, _, hp⟩ :=
    (Order.height_eq_top_iff.mp htop) (Fintype.card L)
  exact (LTSeries.length_lt_card p).ne hp

omit [OrderBot L] [OrderTop L] in
/-- In a finite poset, comparable elements with equal height are equal. -/
lemma eq_of_le_of_height_eq [Fintype L] {x y : L} (hxy : x ≤ y)
    (hh : Order.height x = Order.height y) : x = y := by
  by_contra hne
  have hlt : x < y := lt_of_le_of_ne hxy hne
  exact (ne_of_lt (Order.height_strictMono hlt (finite_height_lt_top x))) hh

lemma joinFace_eq_meetFace_of_boolean {k : ℕ} {H : Fin k → L}
    (hH : IsBooleanTuple H) (S : Finset (Fin k)) :
    joinFace H S = meetFace H S := by
  induction S using Finset.induction_on with
  | empty => simp [joinFace]
  | @insert i S hi ih =>
      calc
        joinFace H (insert i S) =
            commonMeet H ⊔ (reconstructedAtom H i ⊔ S.sup (reconstructedAtom H)) := by
              rw [joinFace, Finset.sup_insert]
        _ = reconstructedAtom H i ⊔
            (commonMeet H ⊔ S.sup (reconstructedAtom H)) := by ac_rfl
        _ = meetFace H {i} ⊔ joinFace H S := by
              rw [reconstructedAtom_eq_meetFace_singleton, joinFace]
        _ = meetFace H {i} ⊔ meetFace H S := by rw [ih]
        _ = meetFace H ({i} ∪ S) := (hH.2 {i} S).symm
        _ = meetFace H (insert i S) := by simp

/--
Theorem 3.1 (`thm:global-gap`), criterion part: the paper's literal ordered
meet map is Boolean exactly when every reconstructed atom rises and all
`2^k` reconstruction height gaps vanish.
-/
theorem global_height_gap_criterion [Fintype L] {k : ℕ} (H : Fin k → L) :
    IsBooleanTuple H ↔
      ReconstructedAtomsRise H ∧ ReconstructionGapsVanish H := by
  constructor
  · intro hH
    constructor
    · intro i
      have hne : commonMeet H ≠ reconstructedAtom H i := by
        intro heq
        have hsets : (∅ : Finset (Fin k)) = {i} := hH.1 (by simpa using heq)
        simp at hsets
      exact Order.height_strictMono
        (lt_of_le_of_ne (commonMeet_le_reconstructedAtom H i) hne)
        (finite_height_lt_top (commonMeet H))
    · intro S
      rw [joinFace_eq_meetFace_of_boolean hH S]
  · rintro ⟨hrise, hgaps⟩
    have hface : ∀ S : Finset (Fin k), joinFace H S = meetFace H S := fun S ↦
      eq_of_le_of_height_eq (joinFace_le_meetFace H S) (hgaps S)
    constructor
    · intro S T hST
      have subset_of_eq : ∀ {S T : Finset (Fin k)},
          meetFace H S = meetFace H T → S ⊆ T := by
        intro S T hEq i hiS
        by_contra hiT
        have hAiS : reconstructedAtom H i ≤ meetFace H S :=
          reconstructedAtom_le_meetFace_of_mem H hiS
        have hTi : meetFace H T ≤ H i := by
          apply Finset.inf_le
          simp [hiT]
        have hAi : reconstructedAtom H i ≤ H i :=
          (hAiS.trans_eq hEq).trans hTi
        have hcollapse : reconstructedAtom H i = commonMeet H := by
          calc
            reconstructedAtom H i = reconstructedAtom H i ⊓ H i :=
              (inf_eq_left.mpr hAi).symm
            _ = commonMeet H := reconstructedAtom_inf_entry H i
        have hstrict := hrise i
        rw [hcollapse] at hstrict
        exact (lt_irrefl _ hstrict)
      exact Finset.Subset.antisymm (subset_of_eq hST) (subset_of_eq hST.symm)
    · intro S T
      rw [← hface (S ∪ T), ← hface S, ← hface T]
      simp only [joinFace, Finset.sup_union]
      ac_rfl

end FiniteLattice

end BooleanAntichainsKernel
