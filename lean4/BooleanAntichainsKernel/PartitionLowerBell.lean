import BooleanAntichainsKernel.PartitionLowerProduct
import BooleanAntichainsKernel.PartitionBellCount
import BooleanAntichainsKernel.PartitionSubsetEquiv

namespace BooleanAntichainsKernel

open scoped Classical

variable {α : Type*} [DecidableEq α]

theorem partitionSubset_card_bell (s : Finset α) :
    Fintype.card (Finpartition s) = Nat.bell s.card := by
  calc
    _ = Fintype.card (Finpartition (Finset.univ : Finset (Fin s.card))) :=
      supportedPartition_count_fin s
    _ = _ := by
      rw [finitePartition_card_bell, Fintype.card_fin]

variable {s : Finset α} (P : Finpartition s)

/-- The manuscript's literal lower-interval cardinal, on actual coarse
blocks and actual Bell numbers of their original cardinalities. -/
theorem partitionLowerInterval_bell_product :
    Fintype.card (Set.Iic P) = ∏ B : P.parts, Nat.bell B.1.card := by
  rw [partitionLowerInterval_count]
  apply Finset.prod_congr rfl
  intro B _hB
  exact partitionSubset_card_bell B.1

theorem partitionLowerInterval_bell_product_sq :
    (Fintype.card (Set.Iic P)) ^ 2 = ∏ B : P.parts, (Nat.bell B.1.card) ^ 2 := by
  rw [partitionLowerInterval_bell_product, Finset.prod_pow]

end BooleanAntichainsKernel
