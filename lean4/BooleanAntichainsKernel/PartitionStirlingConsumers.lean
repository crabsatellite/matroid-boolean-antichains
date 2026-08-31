import BooleanAntichainsKernel.PartitionStirling
import BooleanAntichainsKernel.PartitionContractionBases

namespace BooleanAntichainsKernel

open scoped Classical

theorem completeMatroid_corank_count {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] (k : ℕ) :
    Fintype.card (CorankFlat (cycleMatroid (completeLabelledGraph α)) k) =
      Nat.stirlingSecond (Fintype.card α) (k + 1) := by
  calc
    _ = Fintype.card (PartitionsWithBlocks α (k + 1)) :=
      (Fintype.card_congr (partitionCorankEquiv (α := α) k)).symm
    _ = _ := partitionsWithBlocks_card (k + 1)

theorem completeFinMatroid_corank_count (n : ℕ) (hn : 0 < n) (k : ℕ) :
    Fintype.card (CorankFlat (cycleMatroid (completeLabelledGraph (Fin n))) k) =
      Nat.stirlingSecond n (k + 1) := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  simpa only [Fintype.card_fin] using completeMatroid_corank_count (α := Fin n) k

end BooleanAntichainsKernel
