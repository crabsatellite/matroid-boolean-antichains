import BooleanAntichainsKernel.PartitionStirlingConsumers
import BooleanAntichainsKernel.CompleteGraphCayley

namespace BooleanAntichainsKernel

open scoped Classical

section General

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]

theorem partitionBlockTree_count (P : Finpartition (Finset.univ : Finset α)) :
    Fintype.card (GraphSpanningTrees (completeLabelledGraph P.parts)) =
      P.parts.card ^ (P.parts.card - 2) := by
  letI : Nonempty P.parts := Nonempty.map (finitePartitionBlockOf P) inferInstance
  simpa only [Fintype.card_coe] using completeGraph_spanningTree_count (α := P.parts)

/-- The actual contraction/tree coefficient sum is evaluated using the
proved Cayley count and the proved unordered partition/Stirling count. -/
theorem partitionRankTight_stirling_cayley (k : ℕ) :
    Fintype.card (PartitionRankTightAntichain α k) =
      Nat.stirlingSecond (Fintype.card α) (k + 1) * (k + 1) ^ (k - 1) := by
  rw [partitionRankTight_count_complete_trees]
  have hw (Q : PartitionsWithBlocks α (k + 1)) :
      Fintype.card (GraphSpanningTrees (completeLabelledGraph Q.1.parts)) = (k + 1) ^ (k - 1) := by
    rw [partitionBlockTree_count, Q.2]
    congr 1
  calc
    _ = ∑ _Q : PartitionsWithBlocks α (k + 1), (k + 1) ^ (k - 1) := by
      apply Finset.sum_congr rfl
      intro Q _hQ
      exact hw Q
    _ = Fintype.card (PartitionsWithBlocks α (k + 1)) * (k + 1) ^ (k - 1) := by
      simp only [Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul]
    _ = _ := by rw [partitionsWithBlocks_card]

theorem partitionMaximum_isRankTight
    (C : BooleanAntichain (Fintype.card α - 1) (Finpartition (Finset.univ : Finset α))) :
    IsPartitionRankTight C := by
  apply (partitionAntichain_rankTight_iff C).mp
  have hb := booleanAntichain_bottom_rank_bound (partitionAntichainEquiv (Fintype.card α - 1) C)
  have ht : MatroidFlat.rank (⊤ : MatroidFlat (cycleMatroid (completeLabelledGraph α))) = Fintype.card α - 1 := by
    change matroidRank (cycleMatroid (completeLabelledGraph α)) (cycleMatroid (completeLabelledGraph α)).E = _
    rw [completeLabelledGraph_matroid_rank, Nat.card_eq_fintype_card]
  unfold IsRankTight
  rw [ht] at hb ⊢
  omega

/-- At maximum size the rank-tight subtype contains every actual
Boolean antichain; the equivalence leaves the finite family unchanged. -/
noncomputable def partitionMaximumEquivRankTight :
    BooleanAntichain (Fintype.card α - 1) (Finpartition (Finset.univ : Finset α)) ≃
      PartitionRankTightAntichain α (Fintype.card α - 1) where
  toFun C := ⟨C, partitionMaximum_isRankTight C⟩
  invFun := Subtype.val
  left_inv _ := rfl
  right_inv _ := rfl

theorem partitionMaximum_count :
    Fintype.card (BooleanAntichain (Fintype.card α - 1) (Finpartition (Finset.univ : Finset α))) =
      (Fintype.card α) ^ (Fintype.card α - 2) := by
  rw [Fintype.card_congr (partitionMaximumEquivRankTight (α := α)), partitionRankTight_stirling_cayley]
  have hn : 0 < Fintype.card α := Fintype.card_pos
  have hs : Fintype.card α - 1 + 1 = Fintype.card α := by omega
  have he : Fintype.card α - 1 - 1 = Fintype.card α - 2 := by omega
  rw [hs, he, Nat.stirlingSecond_self, one_mul]

end General

/-- Equation partition-tight with exactly the displayed parameter range. -/
theorem partition_rank_tight_formula (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n - 1) :
    Fintype.card (PartitionRankTightAntichain (Fin n) k) =
      Nat.stirlingSecond n (k + 1) * (k + 1) ^ (k - 1) := by
  have hn : 0 < n := by omega
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  simpa only [Fintype.card_fin] using partitionRankTight_stirling_cayley (α := Fin n) k

theorem partition_fin_maximum_count (n : ℕ) (hn : 0 < n) :
    Fintype.card (BooleanAntichain (n - 1) (Finpartition (Finset.univ : Finset (Fin n)))) = n ^ (n - 2) := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  simpa only [Fintype.card_fin] using partitionMaximum_count (α := Fin n)

end BooleanAntichainsKernel
