import BooleanAntichainsKernel.Core
import Mathlib.Data.Finset.Grade
import Mathlib.Data.Fintype.Powerset
import Mathlib.Order.Preorder.Chain

/-! Full-height rigidity (Lemma 2.1).  The proof counts the strict steps in
the literal Boolean face lattice, exactly as in the manuscript. -/

namespace BooleanAntichainsKernel

open Finset

lemma strictMono_finset_steps {ι : Type*} [DecidableEq ι]
    (f : Finset ι → ℕ) (hf : StrictMono f) (S D : Finset ι)
    (hSD : Disjoint S D) : f S + D.card ≤ f (S ∪ D) := by
  induction D using Finset.induction_on with
  | empty => simp
  | @insert i D hi ih =>
    have hiS : i ∉ S := fun hiS ↦ Finset.disjoint_left.mp hSD hiS (mem_insert_self _ _)
    have hSD' : Disjoint S D := hSD.mono_right (subset_insert _ _)
    have hstep : f (S ∪ D) < f (S ∪ insert i D) := by
      rw [union_insert]
      exact hf (ssubset_insert (by simp [hiS, hi]))
    have hind := ih hSD'
    rw [card_insert_of_notMem hi]
    omega

lemma strictMono_finset_interval_steps {ι : Type*} [DecidableEq ι]
    (f : Finset ι → ℕ) (hf : StrictMono f) {S T : Finset ι} (hST : S ⊆ T) :
    f S + (T \ S).card ≤ f T := by
  simpa [union_sdiff_of_subset hST] using
    strictMono_finset_steps f hf S (T \ S) disjoint_sdiff_self_right

section Lattice

variable {L : Type*} [Lattice L] [OrderTop L]

lemma boolean_meetFace_le_iff {k : ℕ} {H : Fin k → L} (hH : IsBooleanTuple H)
    {S T : Finset (Fin k)} : meetFace H S ≤ meetFace H T ↔ S ⊆ T := by
  constructor
  · intro hle
    have hmeet : meetFace H (S ∩ T) = meetFace H S := by
      rw [meetFace_inter, inf_eq_left.mpr hle]
    exact Finset.inter_eq_left.mp (hH.1 hmeet)
  · intro hST
    exact Finset.inf_mono (Finset.sdiff_subset_sdiff (Finset.Subset.refl _) hST)

lemma boolean_meetFace_strictMono {k : ℕ} {H : Fin k → L}
    (hH : IsBooleanTuple H) : StrictMono (meetFace H) := by
  intro S T hST
  exact lt_of_le_of_ne ((boolean_meetFace_le_iff hH).mpr hST.le)
    (fun heq ↦ hST.ne (hH.1 heq))

lemma boolean_face_rank_bounds {k : ℕ} {H : Fin k → L} (hH : IsBooleanTuple H)
    (ρ : L → ℕ) (hρ : StrictMono ρ) (S : Finset (Fin k)) :
    ρ (commonMeet H) + S.card ≤ ρ (meetFace H S) ∧
      ρ (meetFace H S) + (k - S.card) ≤ ρ ⊤ := by
  have hf : StrictMono (fun T ↦ ρ (meetFace H T)) := hρ.comp (boolean_meetFace_strictMono hH)
  constructor
  · simpa using strictMono_finset_steps _ hf ∅ S (by simp)
  · have hh := strictMono_finset_interval_steps _ hf (subset_univ S)
    simpa [card_sdiff_of_subset (subset_univ S)] using hh

lemma boolean_full_rank_faces {k : ℕ} {H : Fin k → L} (hH : IsBooleanTuple H)
    (ρ : L → ℕ) (hρ : StrictMono ρ) (htop : ρ ⊤ = k) (S : Finset (Fin k)) :
    ρ (meetFace H S) = S.card := by
  obtain ⟨hl, hu⟩ := boolean_face_rank_bounds hH ρ hρ S
  have hcard : S.card ≤ k := by simpa using Finset.card_le_card (subset_univ S)
  rw [htop] at hu
  omega

variable [OrderBot L] [GradeMinOrder ℕ L]

lemma full_height_commonMeet_eq_bot {r : ℕ} {H : Fin r → L}
    (hH : IsBooleanTuple H) (hr : grade ℕ (⊤ : L) = r) : commonMeet H = ⊥ := by
  have hz := boolean_full_rank_faces hH (grade ℕ) grade_strictMono hr ∅
  simp only [meetFace_empty, card_empty] at hz
  apply le_antisymm ?_ _root_.bot_le
  by_contra hnot
  have hh := grade_strictMono (𝕆 := ℕ) (lt_of_le_not_ge _root_.bot_le hnot)
  simp [hz] at hh

omit [OrderBot L] in
lemma full_height_face_grade {r : ℕ} {H : Fin r → L}
    (hH : IsBooleanTuple H) (hr : grade ℕ (⊤ : L) = r) (S : Finset (Fin r)) :
    grade ℕ (meetFace H S) = S.card :=
  boolean_full_rank_faces hH (grade ℕ) grade_strictMono hr S

omit [OrderBot L] in
lemma full_height_atom_grade {r : ℕ} {H : Fin r → L}
    (hH : IsBooleanTuple H) (hr : grade ℕ (⊤ : L) = r) (i : Fin r) :
    grade ℕ (reconstructedAtom H i) = 1 := by
  rw [reconstructedAtom_eq_meetFace_singleton, full_height_face_grade hH hr, card_singleton]

omit [OrderBot L] in
lemma full_height_coatom_grade {r : ℕ} {H : Fin r → L}
    (hH : IsBooleanTuple H) (hr : grade ℕ (⊤ : L) = r) (i : Fin r) :
    grade ℕ (H i) = r - 1 := by
  rw [← meetFace_complement_singleton H i, full_height_face_grade hH hr]
  simp

omit [OrderBot L] in
lemma full_height_cover {r : ℕ} {H : Fin r → L}
    (hH : IsBooleanTuple H) (hr : grade ℕ (⊤ : L) = r)
    {S T : Finset (Fin r)} (hST : S ⋖ T) : meetFace H S ⋖ meetFace H T := by
  refine ⟨boolean_meetFace_strictMono hH hST.lt, ?_⟩
  intro x hSx hxT
  have hsx : grade ℕ (meetFace H S) < grade ℕ x := grade_strictMono hSx
  have hxt : grade ℕ x < grade ℕ (meetFace H T) := grade_strictMono hxT
  rw [full_height_face_grade hH hr] at hsx hxt
  exact hST.card_finset.2 hsx hxt

end Lattice
end BooleanAntichainsKernel
