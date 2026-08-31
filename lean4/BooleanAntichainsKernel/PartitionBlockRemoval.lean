import BooleanAntichainsKernel.PartitionSubsetEquiv

namespace BooleanAntichainsKernel

open scoped Classical

variable {α : Type*} [DecidableEq α] {s C : Finset α}

def partitionRemoveBlock (P : Finpartition s) (C : Finset α) : Finpartition (s \ C) := P.avoid C

theorem partitionRemoveBlock_parts (P : Finpartition s) (hC : C ∈ P.parts) :
    (partitionRemoveBlock P C).parts = P.parts.erase C := by
  ext E
  constructor
  · intro hE
    obtain ⟨D, hD, hnot, hDE⟩ := (Finpartition.mem_avoid (P := P)).mp hE
    have hne : D ≠ C := fun h ↦ hnot h.le
    have hdiff : D \ C = D := Finset.sdiff_eq_self_iff_disjoint.mpr (P.disjoint hD hC hne)
    have hEq : D = E := hdiff.symm.trans hDE
    rw [← hEq]
    exact Finset.mem_erase.mpr ⟨hne, hD⟩
  · intro hE
    obtain ⟨hne, hE⟩ := Finset.mem_erase.mp hE
    have hd : Disjoint E C := P.disjoint hE hC hne
    have hnot : ¬E ⊆ C := fun h ↦ P.ne_empty hE (disjoint_self.mp (hd.mono_right h))
    exact (Finpartition.mem_avoid (P := P)).mpr
      ⟨E, hE, hnot, Finset.sdiff_eq_self_iff_disjoint.mpr hd⟩

def partitionAdjoinBlock (s C : Finset α) (hC : C.Nonempty) (hCs : C ⊆ s)
    (R : Finpartition (s \ C)) : Finpartition s :=
  R.extend hC.ne_empty disjoint_sdiff_self_left (Finset.sdiff_union_of_subset hCs)

theorem partitionAdjoinBlock_parts (s C : Finset α) (hC : C.Nonempty) (hCs : C ⊆ s)
    (R : Finpartition (s \ C)) :
    (partitionAdjoinBlock s C hC hCs R).parts = insert C R.parts := rfl

theorem partitionAdjoinBlock_mem (s C : Finset α) (hC : C.Nonempty) (hCs : C ⊆ s)
    (R : Finpartition (s \ C)) : C ∈ (partitionAdjoinBlock s C hC hCs R).parts :=
  Finset.mem_insert_self _ _

theorem partitionComplement_block_notMem (s C : Finset α) (hC : C.Nonempty)
    (R : Finpartition (s \ C)) : C ∉ R.parts := by
  intro h
  obtain ⟨x, hx⟩ := hC
  exact (Finset.mem_sdiff.mp (R.le h hx)).2 hx

/-- Restore the exact original block family after deleting a marked block. -/
theorem partitionAdjoin_remove (P : Finpartition s) (hC : C ∈ P.parts) :
    partitionAdjoinBlock s C (P.nonempty_of_mem_parts hC) (P.le hC) (partitionRemoveBlock P C) = P := by
  apply Finpartition.ext
  rw [partitionAdjoinBlock_parts, partitionRemoveBlock_parts P hC]
  exact Finset.insert_erase hC

/-- Deleting the freshly adjoined block restores every remaining block. -/
theorem partitionRemove_adjoin (s C : Finset α) (hC : C.Nonempty) (hCs : C ⊆ s)
    (R : Finpartition (s \ C)) :
    partitionRemoveBlock (partitionAdjoinBlock s C hC hCs R) C = R := by
  apply Finpartition.ext
  rw [partitionRemoveBlock_parts _ (partitionAdjoinBlock_mem s C hC hCs R), partitionAdjoinBlock_parts]
  exact Finset.erase_insert (partitionComplement_block_notMem s C hC R)

theorem partitionRemoveBlock_card (P : Finpartition s) (hC : C ∈ P.parts) :
    (partitionRemoveBlock P C).parts.card = P.parts.card - 1 := by
  rw [partitionRemoveBlock_parts P hC, Finset.card_erase_of_mem hC]

theorem partitionAdjoinBlock_card (s C : Finset α) (hC : C.Nonempty) (hCs : C ⊆ s)
    (R : Finpartition (s \ C)) :
    (partitionAdjoinBlock s C hC hCs R).parts.card = R.parts.card + 1 := by
  rw [partitionAdjoinBlock_parts, Finset.card_insert_of_notMem (partitionComplement_block_notMem s C hC R)]

end BooleanAntichainsKernel
