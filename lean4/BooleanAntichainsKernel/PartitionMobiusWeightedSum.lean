import BooleanAntichainsKernel.PartitionMobiusIdentity
import BooleanAntichainsKernel.PartitionStirling
import BooleanAntichainsKernel.PartitionCoarseningBlocks

namespace BooleanAntichainsKernel

open scoped Classical

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem partitionMobius_inner_sum (P : Finpartition (Finset.univ : Finset α)) :
    (∑ k ∈ Finset.range (Fintype.card α + 1),
      if k = P.parts.card then partitionMobiusCandidate k else 0) =
        partitionMobiusCandidate P.parts.card := by
  have hmem : P.parts.card ∈ Finset.range (Fintype.card α + 1) :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le (by
      simpa only [Finset.card_univ] using P.card_parts_le_card))
  rw [Finset.sum_ite_eq', if_pos hmem]

theorem partitionMobius_stratum_sum (k : ℕ) :
    (∑ P : Finpartition (Finset.univ : Finset α),
      if k = P.parts.card then partitionMobiusCandidate k else 0) =
        (Nat.stirlingSecond (Fintype.card α) k : ℤ) * partitionMobiusCandidate k := by
  have hc := partition_card_subtype_indicator
    (fun P : Finpartition (Finset.univ : Finset α) ↦ P.parts.card = k)
  have hc' : (∑ P : Finpartition (Finset.univ : Finset α),
      if P.parts.card = k then (1 : ℤ) else 0) =
      (Fintype.card (PartitionsWithBlocks α k) : ℤ) := by
    exact_mod_cast hc.symm
  calc
    _ = ∑ P : Finpartition (Finset.univ : Finset α),
        (if P.parts.card = k then (1 : ℤ) else 0) * partitionMobiusCandidate k := by
      apply Finset.sum_congr rfl
      intro P _hP
      by_cases h : P.parts.card = k
      · simp [h]
      · have hk : k ≠ P.parts.card := fun hk ↦ h hk.symm
        simp [h, hk]
    _ = (∑ P : Finpartition (Finset.univ : Finset α),
        if P.parts.card = k then (1 : ℤ) else 0) * partitionMobiusCandidate k := by
      rw [Finset.sum_mul]
    _ = (Fintype.card (PartitionsWithBlocks α k) : ℤ) * partitionMobiusCandidate k := by
      rw [hc']
    _ = _ := by rw [partitionsWithBlocks_card]

theorem finitePartition_mobius_weighted_sum :
    (∑ P : Finpartition (Finset.univ : Finset α), partitionMobiusCandidate P.parts.card) =
      partitionMobiusConvolution (Fintype.card α) := by
  calc
    _ = ∑ P : Finpartition (Finset.univ : Finset α),
        ∑ k ∈ Finset.range (Fintype.card α + 1),
          if k = P.parts.card then partitionMobiusCandidate k else 0 := by
      apply Finset.sum_congr rfl
      intro P _hP
      exact (partitionMobius_inner_sum P).symm
    _ = ∑ k ∈ Finset.range (Fintype.card α + 1),
        ∑ P : Finpartition (Finset.univ : Finset α),
          if k = P.parts.card then partitionMobiusCandidate k else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ k ∈ Finset.range (Fintype.card α + 1),
        (Nat.stirlingSecond (Fintype.card α) k : ℤ) * partitionMobiusCandidate k := by
      apply Finset.sum_congr rfl
      intro k _hk
      exact partitionMobius_stratum_sum k
    _ = _ := rfl

theorem partitionCoarsening_mobius_weighted_sum
    (P : Finpartition (Finset.univ : Finset α)) :
    (∑ Q : Set.Ici P, partitionMobiusCandidate Q.1.parts.card) =
      partitionMobiusConvolution P.parts.card := by
  calc
    _ = ∑ Q : Set.Ici P,
        partitionMobiusCandidate ((partitionCoarseningOrderIso P Q).parts.card) := by
      apply Finset.sum_congr rfl
      intro Q _hQ
      rw [partitionCoarsening_blocks_card]
    _ = ∑ R : Finpartition (Finset.univ : Finset P.parts),
        partitionMobiusCandidate R.parts.card := by
      have h := (partitionCoarseningOrderIso P).sum_comp
        (fun R : Finpartition (Finset.univ : Finset P.parts) ↦
          partitionMobiusCandidate R.parts.card)
      exact h
    _ = partitionMobiusConvolution (Fintype.card P.parts) :=
      finitePartition_mobius_weighted_sum
    _ = _ := by rw [Fintype.card_coe]

end BooleanAntichainsKernel
