import BooleanAntichainsKernel.PartitionBlockRemoval
import BooleanAntichainsKernel.PartitionInsertBijection
import Mathlib.Data.Fintype.BigOperators

namespace BooleanAntichainsKernel

open scoped Classical

abbrev MarkedPartition (α : Type*) [Fintype α] [DecidableEq α] :=
  {t : Finpartition (Finset.univ : Finset α) × Finset α // t.2 ∈ t.1.parts}

abbrev RemovedPartitionBlockData (α : Type*) [Fintype α] [DecidableEq α] :=
  Σ C : {C : Finset α // C.Nonempty}, Finpartition ((Finset.univ : Finset α) \ C.1)

variable {α : Type*} [Fintype α] [DecidableEq α]

def markedPartitionSigmaEquiv :
    (Σ P : Finpartition (Finset.univ : Finset α), P.parts) ≃ MarkedPartition α where
  toFun t := ⟨(t.1, t.2.1), t.2.2⟩
  invFun t := ⟨t.1.1, ⟨t.1.2, t.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

def markedPartitionRemove : MarkedPartition α → RemovedPartitionBlockData α
  | ⟨⟨P, C⟩, hC⟩ =>
      ⟨⟨C, P.nonempty_of_mem_parts hC⟩, partitionRemoveBlock P C⟩

def removedPartitionBlockInsert : RemovedPartitionBlockData α → MarkedPartition α
  | ⟨C, R⟩ =>
      ⟨(partitionAdjoinBlock Finset.univ C.1 C.2 (Finset.subset_univ _) R, C.1),
        partitionAdjoinBlock_mem Finset.univ C.1 C.2 (Finset.subset_univ _) R⟩

theorem markedPartitionInsert_remove (t : MarkedPartition α) :
    removedPartitionBlockInsert (markedPartitionRemove t) = t := by
  rcases t with ⟨⟨P, C⟩, hC⟩
  apply Subtype.ext
  exact Prod.ext (partitionAdjoin_remove P hC) rfl

theorem markedPartitionRemove_insert (t : RemovedPartitionBlockData α) :
    markedPartitionRemove (removedPartitionBlockInsert t) = t := by
  rcases t with ⟨C, R⟩
  rcases C with ⟨C, hC⟩
  change (⟨⟨C, _⟩, partitionRemoveBlock
    (partitionAdjoinBlock Finset.univ C hC (Finset.subset_univ _) R) C⟩ :
      RemovedPartitionBlockData α) = ⟨⟨C, hC⟩, R⟩
  congr 1
  exact partitionRemove_adjoin Finset.univ C hC (Finset.subset_univ _) R

/-- Marking a genuine block is equivalent to choosing its exact nonempty
vertex subset and a partition of its exact complement. -/
def markedPartitionRemovedEquiv : MarkedPartition α ≃ RemovedPartitionBlockData α where
  toFun := markedPartitionRemove
  invFun := removedPartitionBlockInsert
  left_inv := markedPartitionInsert_remove
  right_inv := markedPartitionRemove_insert

def partitionSigmaOptionEquiv :
    (Σ P : Finpartition (Finset.univ : Finset α), Option P.parts) ≃
      Finpartition (Finset.univ : Finset α) ⊕ (Σ P : Finpartition (Finset.univ : Finset α), P.parts) where
  toFun t := match t.2 with
    | none => Sum.inl t.1
    | some B => Sum.inr ⟨t.1, B⟩
  invFun t := match t with
    | Sum.inl P => ⟨P, none⟩
    | Sum.inr t => ⟨t.1, some t.2⟩
  left_inv t := by rcases t with ⟨P, t⟩; cases t <;> rfl
  right_inv t := by cases t <;> rfl

noncomputable def partitionOptionBlockEquiv :
    Finpartition (Finset.univ : Finset (Option α)) ≃
      Finpartition (Finset.univ : Finset α) ⊕ RemovedPartitionBlockData α :=
  partitionInsertEquiv.symm.trans
    (partitionSigmaOptionEquiv.trans
      (Equiv.sumCongr (Equiv.refl _) (markedPartitionSigmaEquiv.trans markedPartitionRemovedEquiv)))

theorem partition_option_total_split :
    Fintype.card (Finpartition (Finset.univ : Finset (Option α))) =
      Fintype.card (Finpartition (Finset.univ : Finset α)) +
        ∑ C : {C : Finset α // C.Nonempty}, Fintype.card (Finpartition ((Finset.univ : Finset α) \ C.1)) := by
  rw [Fintype.card_congr (partitionOptionBlockEquiv (α := α)), Fintype.card_sum, Fintype.card_sigma]

end BooleanAntichainsKernel
