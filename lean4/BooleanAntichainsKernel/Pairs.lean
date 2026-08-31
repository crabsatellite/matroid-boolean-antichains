import BooleanAntichainsKernel.GlobalEnumerator

/-!
# Two-element Boolean antichains

This file proves the structural half of manuscript `thm:size-two` directly from
the four literal meet faces.  The Möbius-inversion count is kept separate so
that its incidence-algebra dependency is auditable.
-/

namespace BooleanAntichainsKernel

open Finset

section Pair

variable {L : Type*} [Lattice L] [OrderBot L] [OrderTop L]

def pairTuple (F G : L) : Fin 2 → L := fun i ↦ if i = 0 then F else G

omit [Lattice L] [OrderBot L] [OrderTop L] in
@[simp] lemma pairTuple_zero (F G : L) : pairTuple F G 0 = F := by
  simp [pairTuple]

omit [Lattice L] [OrderBot L] [OrderTop L] in
@[simp] lemma pairTuple_one (F G : L) : pairTuple F G 1 = G := by
  simp [pairTuple]

omit [OrderBot L] in
lemma pair_meetFace (F G : L) (S : Finset (Fin 2)) :
    meetFace (pairTuple F G) S =
      (if (0 : Fin 2) ∈ S then ⊤ else F) ⊓
      (if (1 : Fin 2) ∈ S then ⊤ else G) := by
  have hu : (Finset.univ : Finset (Fin 2)) = {0, 1} := by decide
  rw [meetFace, hu]
  by_cases h0 : (0 : Fin 2) ∈ S
  · by_cases h1 : (1 : Fin 2) ∈ S
    · have hs : ({0, 1} : Finset (Fin 2)) \ S = ∅ := by
        ext i
        fin_cases i <;> simp [h0, h1]
      simp [h0, h1, hs]
    · have hs : ({0, 1} : Finset (Fin 2)) \ S = {1} := by
        ext i
        fin_cases i <;> simp [h0, h1]
      simp [h0, h1, hs]
  · by_cases h1 : (1 : Fin 2) ∈ S
    · have hs : ({0, 1} : Finset (Fin 2)) \ S = {0} := by
        ext i
        fin_cases i <;> simp [h0, h1]
      simp [h0, h1, hs]
    · have hs : ({0, 1} : Finset (Fin 2)) \ S = {0, 1} := by
        ext i
        fin_cases i <;> simp [h0, h1]
      simp [h0, h1, hs, pairTuple]

omit [OrderBot L] in
lemma booleanTuple_entry_ne_top {k : ℕ} {H : Fin k → L}
    (hH : IsBooleanTuple H) (i : Fin k) : H i ≠ ⊤ := by
  intro hi
  have hfaces : meetFace H (Finset.univ.erase i) = meetFace H Finset.univ := by
    simpa using hi
  have herase : Finset.univ.erase i = (Finset.univ : Finset (Fin k)) := hH.1 hfaces
  exact Finset.notMem_erase i Finset.univ (herase.symm ▸ Finset.mem_univ i)

omit [OrderBot L] in
/-- The structural equivalence in `thm:size-two`. -/
theorem pair_isBoolean_iff (F G : L) :
    IsBooleanTuple (pairTuple F G) ↔ F ≠ ⊤ ∧ G ≠ ⊤ ∧ F ⊔ G = ⊤ := by
  constructor
  · intro h
    refine ⟨booleanTuple_entry_ne_top h 0,
      booleanTuple_entry_ne_top h 1, ?_⟩
    have hj := h.2 ({0} : Finset (Fin 2)) {1}
    simpa [pair_meetFace, sup_comm] using hj.symm
  · rintro ⟨hF, hG, hsup⟩
    have hFG : ¬F ≤ G := by
      intro hle
      apply hG
      rw [← hsup, sup_eq_right.mpr hle]
    have hGF : ¬G ≤ F := by
      intro hle
      apply hF
      rw [← hsup, sup_eq_left.mpr hle]
    have hFGne : F ≠ G := fun h ↦ hFG h.le
    have hInfTop : F ⊓ G ≠ ⊤ := by
      intro h
      apply hF
      exact top_unique (h ▸ inf_le_left)
    have htopF : (⊤ : L) ≠ F := hF.symm
    have htopG : (⊤ : L) ≠ G := hG.symm
    have htopInf : (⊤ : L) ≠ F ⊓ G := hInfTop.symm
    have hGFne : G ≠ F := hFGne.symm
    constructor
    · intro S T hST
      have hface := hST
      rw [pair_meetFace, pair_meetFace] at hface
      by_cases hS0 : (0 : Fin 2) ∈ S <;>
        by_cases hS1 : (1 : Fin 2) ∈ S <;>
        by_cases hT0 : (0 : Fin 2) ∈ T <;>
        by_cases hT1 : (1 : Fin 2) ∈ T
      all_goals
        simp [hS0, hS1, hT0, hT1, hF, hG, hFGne, hGFne,
          hInfTop, htopF, htopG, htopInf] at hface
      all_goals
        try contradiction
      all_goals
        ext i
        fin_cases i <;> simp [hS0, hS1, hT0, hT1]
    · intro S T
      rw [pair_meetFace, pair_meetFace, pair_meetFace]
      by_cases hS0 : (0 : Fin 2) ∈ S <;>
        by_cases hS1 : (1 : Fin 2) ∈ S <;>
        by_cases hT0 : (0 : Fin 2) ∈ T <;>
        by_cases hT1 : (1 : Fin 2) ∈ T <;>
        simp [hS0, hS1, hT0, hT1, hsup, sup_comm]

end Pair

end BooleanAntichainsKernel
