import BooleanAntichainsKernel.PartitionExponentialFormula

namespace BooleanAntichainsKernel

open scoped Classical

/-- The displayed partition-pairs formula over ℚ, for the positive
partition-lattice range. The coefficient is the literal coefficient of
the actual formal log(1+A). -/
theorem partition_pairs_log_formula (n : ℕ) (hn : 0 < n) :
    (Fintype.card
      (BooleanAntichain 2 (Finpartition (Finset.univ : Finset (Fin n)))) : ℚ) =
      (1 / 2 : ℚ) * ((n.factorial : ℚ) *
        PowerSeries.coeff n bellSquareLogSeries - 2 * (Nat.bell n : ℚ) + 1) := by
  have hZ := partition_pairs_mobius_doubled n hn
  have hQ :
      (2 : ℚ) * Fintype.card
        (BooleanAntichain 2 (Finpartition (Finset.univ : Finset (Fin n)))) =
      (partitionBellSquareMobiusSum n : ℚ) - 2 * (Nat.bell n : ℚ) + 1 := by
    exact_mod_cast hZ
  rw [partition_exponential_formula_integer_cast] at hQ
  linarith

theorem partition_pairs_log_formula_doubled (n : ℕ) (hn : 0 < n) :
    (2 : ℚ) * Fintype.card
      (BooleanAntichain 2 (Finpartition (Finset.univ : Finset (Fin n)))) =
      (n.factorial : ℚ) * PowerSeries.coeff n bellSquareLogSeries -
        2 * (Nat.bell n : ℚ) + 1 := by
  rw [partition_pairs_log_formula n hn]
  ring

end BooleanAntichainsKernel
