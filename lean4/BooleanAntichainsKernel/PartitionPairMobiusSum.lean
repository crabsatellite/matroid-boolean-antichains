import BooleanAntichainsKernel.PartitionMobius
import BooleanAntichainsKernel.PartitionLowerBell
import BooleanAntichainsKernel.MobiusFormula

namespace BooleanAntichainsKernel

open scoped Classical

noncomputable local instance partitionPairLocallyFiniteOrder {α : Type*}
    [Fintype α] [DecidableEq α] :
    LocallyFiniteOrder (Finpartition (Finset.univ : Finset α)) :=
  Fintype.toLocallyFiniteOrder

noncomputable def partitionBellSquareMobiusSum (n : ℕ) : ℤ :=
  ∑ P : Finpartition (Finset.univ : Finset (Fin n)),
    partitionMobiusCandidate P.parts.card *
      (∏ B : P.parts, (Nat.bell B.1.card : ℤ) ^ 2)

theorem lowerIntervalCard_partition {α : Type*} [Fintype α] [DecidableEq α]
    (P : Finpartition (Finset.univ : Finset α)) :
    lowerIntervalCard P = ∏ B : P.parts, Nat.bell B.1.card := by
  letI : Fintype (Set.Iic P) := Subtype.fintype _
  unfold lowerIntervalCard
  have hc : Fintype.card (Set.Iic P) = (Finset.Iic P).card :=
    Fintype.card_of_finset' (Finset.Iic P) (by simp)
  rw [← hc, partitionLowerInterval_bell_product]

theorem partition_mobiusPairSum_eq (n : ℕ) (hn : 0 < n) :
    mobiusPairSum (L := Finpartition (Finset.univ : Finset (Fin n))) =
      partitionBellSquareMobiusSum n := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  unfold mobiusPairSum partitionBellSquareMobiusSum
  rw [Finset.Iic_top]
  apply Finset.sum_congr rfl
  intro P _hP
  rw [finitePartition_mu_top, lowerIntervalCard_partition]
  push_cast
  rw [Finset.prod_pow]

theorem partition_pairs_mobius_doubled (n : ℕ) (hn : 0 < n) :
    2 * (Fintype.card
        (BooleanAntichain 2 (Finpartition (Finset.univ : Finset (Fin n)))) : ℤ) =
      partitionBellSquareMobiusSum n - 2 * (Nat.bell n : ℤ) + 1 := by
  have h := mobius_formula_pairs_doubled
    (L := Finpartition (Finset.univ : Finset (Fin n)))
  rw [partition_mobiusPairSum_eq n hn] at h
  have hc : Fintype.card (Finpartition (Finset.univ : Finset (Fin n))) = Nat.bell n := by
    simpa only [Fintype.card_fin] using finitePartition_card_bell (α := Fin n)
  rw [hc] at h
  exact h

theorem partition_pairs_mobius_formula (n : ℕ) (hn : 0 < n) :
    (Fintype.card
        (BooleanAntichain 2 (Finpartition (Finset.univ : Finset (Fin n)))) : ℤ) =
      (partitionBellSquareMobiusSum n - 2 * (Nat.bell n : ℤ) + 1) / 2 := by
  rw [← partition_pairs_mobius_doubled n hn, Int.mul_ediv_cancel_left]
  norm_num

end BooleanAntichainsKernel
