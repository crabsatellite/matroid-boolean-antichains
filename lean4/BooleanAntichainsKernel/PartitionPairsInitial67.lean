import BooleanAntichainsKernel.PartitionPairsInitial45
import BooleanAntichainsKernel.PartitionLogSmall67

namespace BooleanAntichainsKernel

theorem partitionPairCount_six : PartitionPairCount 6 = 9750 := by
  have h := partition_pairs_log_formula_doubled 6 (by omega)
  rw [bellSquareLogSeries_coeff_rec, bellSquareLogCoeffRec_six,
    partitionBell_six] at h
  have hf : ((Nat.factorial 6 : ℕ) : ℚ) = 720 := by norm_num [Nat.factorial]
  rw [hf] at h
  ring_nf at h
  have hz : (Fintype.card
    (BooleanAntichain 2 (Finpartition (Finset.univ : Finset (Fin 6)))) : ℚ) = 9750 := by
    linarith
  exact_mod_cast hz

theorem partitionPairCount_seven : PartitionPairCount 7 = 183680 := by
  have h := partition_pairs_log_formula_doubled 7 (by omega)
  rw [bellSquareLogSeries_coeff_rec, bellSquareLogCoeffRec_seven,
    partitionBell_seven] at h
  have hf : ((Nat.factorial 7 : ℕ) : ℚ) = 5040 := by norm_num [Nat.factorial]
  rw [hf] at h
  ring_nf at h
  have hz : (Fintype.card
    (BooleanAntichain 2 (Finpartition (Finset.univ : Finset (Fin 7)))) : ℚ) = 183680 := by
    linarith
  exact_mod_cast hz

theorem partitionPairCount_initial :
    List.ofFn (fun i : Fin 7 ↦ PartitionPairCount (i.1 + 1)) =
      [0, 0, 3, 45, 620, 9750, 183680] := by
  change [PartitionPairCount 1, PartitionPairCount 2, PartitionPairCount 3,
    PartitionPairCount 4, PartitionPairCount 5, PartitionPairCount 6,
    PartitionPairCount 7] = _
  simp [partitionPairCount_one, partitionPairCount_two,
    partitionPairCount_three, partitionPairCount_four, partitionPairCount_five,
    partitionPairCount_six, partitionPairCount_seven]

end BooleanAntichainsKernel
