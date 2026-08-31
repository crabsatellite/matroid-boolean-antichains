import BooleanAntichainsKernel.UnorderedFullHeight
import BooleanAntichainsKernel.AtomCoatomReconstruction

/-! Identify reconstructed atoms with the literal atoms of the Boolean span.
The atomicity predicate is the usual minimal-nonbottom property inside the
actual span, not a definition in terms of reconstructed candidates. -/

namespace BooleanAntichainsKernel

open Set Finset
open scoped Classical

variable {L : Type*} [Lattice L] [OrderBot L] [OrderTop L]

def IsTupleSpanAtom {k : ℕ} (H : Fin k → L) (a : L) : Prop :=
  a ∈ Set.range (meetFace H) ∧ a ≠ commonMeet H ∧
    ∀ b ∈ Set.range (meetFace H), b < a → b = commonMeet H

omit [OrderBot L] in
theorem isTupleSpanAtom_iff {k : ℕ} {H : Fin k → L} (hH : IsBooleanTuple H) (a : L) :
    IsTupleSpanAtom H a ↔ ∃ i, a = reconstructedAtom H i := by
  constructor
  · rintro ⟨⟨S, rfl⟩, hne, hmin⟩
    have hS : S.Nonempty := by
      apply Finset.nonempty_iff_ne_empty.mpr
      intro hs
      apply hne
      simp [hs]
    obtain ⟨i, hiS⟩ := hS
    have his : ({i} : Finset (Fin k)) ⊆ S := Finset.singleton_subset_iff.mpr hiS
    by_cases hs : S = {i}
    · exact ⟨i, by rw [hs, ← reconstructedAtom_eq_meetFace_singleton]⟩
    · have hlt := boolean_meetFace_strictMono hH (lt_of_le_of_ne his (Ne.symm hs))
      have heq := hmin (meetFace H {i}) ⟨{i}, rfl⟩ hlt
      have hsets : ({i} : Finset (Fin k)) = ∅ := hH.1 (by simpa using heq)
      simp at hsets
  · rintro ⟨i, rfl⟩
    refine ⟨⟨{i}, (reconstructedAtom_eq_meetFace_singleton H i).symm⟩, ?_, ?_⟩
    · intro heq
      have hsets : ({i} : Finset (Fin k)) = ∅ := hH.1 (by simpa using heq)
      simp at hsets
    · rintro b ⟨T, rfl⟩ hlt
      rw [reconstructedAtom_eq_meetFace_singleton] at hlt
      have hsub : T ⊆ ({i} : Finset (Fin k)) := (boolean_meetFace_le_iff hH).mp hlt.le
      have hne : T ≠ ({i} : Finset (Fin k)) := fun heq ↦ hlt.ne (congrArg (meetFace H) heq)
      rw [Finset.eq_empty_of_ssubset_singleton (lt_of_le_of_ne hsub hne), meetFace_empty]

variable [DecidableEq L]

/-- Atomicity in the actual unordered span, relative to its own bottom. -/
def IsSpanAtom (C : Finset L) (a : L) : Prop :=
  a ∈ antichainSpan C ∧ a ≠ C.inf id ∧
    ∀ b ∈ antichainSpan C, b < a → b = C.inf id

omit [OrderBot L] in
theorem isSpanAtom_iff_mem_antichainAtoms (C : Finset L) (hC : IsBooleanAntichain C) (a : L) :
    IsSpanAtom C a ↔ a ∈ antichainAtoms C := by
  let e : Fin C.card ≃ C := (Finset.equivFin C).symm
  let H : Fin C.card → L := fun i ↦ (e i).1
  have hH : IsBooleanTuple H := (isBooleanTuple_iff_antichain_of_equiv C e).mpr hC
  have hspan : Set.range (meetFace H) = antichainSpan C := enumeration_span C e
  have hbottom : commonMeet H = C.inf id := enumeration_commonMeet C e
  have hp : IsSpanAtom C a ↔ IsTupleSpanAtom H a := by
    simp only [IsSpanAtom, IsTupleSpanAtom, hspan, hbottom]
  have hcarrier : orderedCarrier H = C := orderedCarrier_of_equiv C e
  have hats : antichainAtoms C = orderedCarrier (reconstructedAtom H) :=
    (congrArg antichainAtoms hcarrier).symm.trans
      (antichainAtoms_orderedCarrier H (isBooleanTuple_injective hH))
  rw [hp, isTupleSpanAtom_iff hH]
  rw [hats]
  simp only [orderedCarrier, Finset.mem_image, Finset.mem_univ, true_and, eq_comm]

noncomputable def spanAtomFinset [Fintype L] (C : Finset L) : Finset L :=
  Finset.univ.filter (IsSpanAtom C)

omit [OrderBot L] in
theorem spanAtomFinset_eq_antichainAtoms [Fintype L] (C : Finset L) (hC : IsBooleanAntichain C) :
    spanAtomFinset C = antichainAtoms C := by
  ext a
  simp only [spanAtomFinset, Finset.mem_filter, Finset.mem_univ, true_and,
    isSpanAtom_iff_mem_antichainAtoms C hC]

end BooleanAntichainsKernel
