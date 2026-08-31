import BooleanAntichainsKernel.PartitionPairsFormula

namespace BooleanAntichainsKernel

open scoped Classical

def bellSquarePowerCoeffRec : ℕ → ℕ → ℚ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | b + 1, n => ∑ ij ∈ Finset.antidiagonal n,
      bellSquarePowerCoeffRec b ij.1 * bellSquareEGFCoeff ij.2

theorem bellSquarePowerCoeffRec_zero (n : ℕ) :
    bellSquarePowerCoeffRec 0 n = if n = 0 then 1 else 0 := by
  cases n <;> rfl

theorem bellSquarePowerCoeffRec_succ (b n : ℕ) :
    bellSquarePowerCoeffRec (b + 1) n = ∑ ij ∈ Finset.antidiagonal n,
      bellSquarePowerCoeffRec b ij.1 * bellSquareEGFCoeff ij.2 := rfl

theorem bellSquareEGF_coeff_pow_rec (b n : ℕ) :
    PowerSeries.coeff n (bellSquareEGF ^ b) = bellSquarePowerCoeffRec b n := by
  induction b generalizing n with
  | zero =>
    cases n <;> simp [bellSquarePowerCoeffRec_zero]
  | succ b ih =>
    rw [pow_succ, PowerSeries.coeff_mul, bellSquarePowerCoeffRec_succ]
    apply Finset.sum_congr rfl
    intro ij _hij
    rw [ih ij.1, bellSquareEGF_coeff]

def bellSquareLogCoeffRec (n : ℕ) : ℚ :=
  ∑ b ∈ Finset.range (n + 1),
    (if b = 0 then 0 else ((-1 : ℚ) ^ (b + 1) / b)) *
      bellSquarePowerCoeffRec b n

theorem bellSquareLogSeries_coeff_rec (n : ℕ) :
    PowerSeries.coeff n bellSquareLogSeries = bellSquareLogCoeffRec n := by
  rw [bellSquareLogSeries_coeff, bellSquareLogCoeffRec]
  apply Finset.sum_congr rfl
  intro b _hb
  rw [bellSquareEGF_coeff_pow_rec]

end BooleanAntichainsKernel
