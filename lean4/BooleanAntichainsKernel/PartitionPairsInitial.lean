import BooleanAntichainsKernel.PartitionPairsFormula
import BooleanAntichainsKernel.BellSquareCoefficientRecurrence

namespace BooleanAntichainsKernel

open scoped Classical

noncomputable def PartitionPairCount (n : ℕ) :=
  Fintype.card (BooleanAntichain 2 (Finpartition (Finset.univ : Finset (Fin n))))

theorem partitionPairCount_zero_of_le_two (n : ℕ) (hn0 : 0 < n) (hn : n ≤ 2) :
    PartitionPairCount n = 0 := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn0⟩⟩
  letI : IsEmpty
      (BooleanAntichain 2 (Finpartition (Finset.univ : Finset (Fin n)))) := ⟨fun C ↦ by
    have hb := booleanAntichain_bottom_rank_bound (partitionAntichainEquiv 2 C)
    have ht : MatroidFlat.rank
        (⊤ : MatroidFlat (cycleMatroid (completeLabelledGraph (Fin n)))) = n - 1 := by
      change matroidRank (cycleMatroid (completeLabelledGraph (Fin n)))
        (cycleMatroid (completeLabelledGraph (Fin n))).E = _
      rw [completeLabelledGraph_matroid_rank, Nat.card_eq_fintype_card, Fintype.card_fin]
    rw [ht] at hb
    omega⟩
  exact Fintype.card_eq_zero

theorem partitionPairCount_one : PartitionPairCount 1 = 0 := by
  exact partitionPairCount_zero_of_le_two 1 (by omega) (by omega)

theorem partitionPairCount_two : PartitionPairCount 2 = 0 := by
  exact partitionPairCount_zero_of_le_two 2 (by omega) (by omega)

theorem partitionPairCount_three : PartitionPairCount 3 = 3 := by
  have h := partition_pairs_log_formula_doubled 3 (by omega)
  have hb : Nat.bell 3 = 5 := by
    rw [show 3 = 2 + 1 by omega, Nat.bell_succ, ← Nat.range_succ_eq_Iic]
    norm_num [Finset.sum_range_succ]
  have hfNat : Nat.factorial 3 = 6 := by norm_num [Nat.factorial]
  have hc : bellSquareLogCoeffRec 3 = 5 / 2 := by
    norm_num [bellSquareLogCoeffRec, bellSquarePowerCoeffRec,
      bellSquareEGFCoeff, Finset.Nat.antidiagonal_eq_map,
      Finset.sum_range_succ, hb, hfNat]
  rw [bellSquareLogSeries_coeff_rec, hc] at h
  rw [hb] at h
  have hf : ((Nat.factorial 3 : ℕ) : ℚ) = 6 := by norm_num [hfNat]
  rw [hf] at h
  ring_nf at h
  have hz : (Fintype.card
    (BooleanAntichain 2 (Finpartition (Finset.univ : Finset (Fin 3)))) : ℚ) = 3 := by
    linarith
  exact_mod_cast hz

end BooleanAntichainsKernel
