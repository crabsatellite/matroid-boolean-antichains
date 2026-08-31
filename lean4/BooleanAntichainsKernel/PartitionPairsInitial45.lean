import BooleanAntichainsKernel.PartitionPairsInitial
import BooleanAntichainsKernel.PartitionLogSmall

namespace BooleanAntichainsKernel

theorem partitionPairCount_four : PartitionPairCount 4 = 45 := by
  have h := partition_pairs_log_formula_doubled 4 (by omega)
  rw [bellSquareLogSeries_coeff_rec, bellSquareLogCoeffRec_four,
    partitionBell_four] at h
  have hf : ((Nat.factorial 4 : ℕ) : ℚ) = 24 := by norm_num [Nat.factorial]
  rw [hf] at h
  ring_nf at h
  have hz : (Fintype.card
    (BooleanAntichain 2 (Finpartition (Finset.univ : Finset (Fin 4)))) : ℚ) = 45 := by
    linarith
  exact_mod_cast hz

theorem partitionPairCount_five : PartitionPairCount 5 = 620 := by
  have h := partition_pairs_log_formula_doubled 5 (by omega)
  rw [bellSquareLogSeries_coeff_rec, bellSquareLogCoeffRec_five,
    partitionBell_five] at h
  have hf : ((Nat.factorial 5 : ℕ) : ℚ) = 120 := by norm_num [Nat.factorial]
  rw [hf] at h
  ring_nf at h
  have hz : (Fintype.card
    (BooleanAntichain 2 (Finpartition (Finset.univ : Finset (Fin 5)))) : ℚ) = 620 := by
    linarith
  exact_mod_cast hz

end BooleanAntichainsKernel
