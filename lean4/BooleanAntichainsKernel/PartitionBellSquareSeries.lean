import BooleanAntichainsKernel.PartitionPairMobiusSum
import Mathlib.RingTheory.PowerSeries.Log
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.Algebra.BigOperators.Finprod

namespace BooleanAntichainsKernel

open scoped Classical

def bellSquareEGFCoeff (n : ℕ) : ℚ :=
  if n = 0 then 0 else (Nat.bell n : ℚ) ^ 2 / n.factorial

noncomputable def bellSquareEGF : PowerSeries ℚ :=
  PowerSeries.mk bellSquareEGFCoeff

@[simp] theorem bellSquareEGF_coeff (n : ℕ) :
    PowerSeries.coeff n bellSquareEGF = bellSquareEGFCoeff n := by
  rw [bellSquareEGF, PowerSeries.coeff_mk]

@[simp] theorem bellSquareEGF_constantCoeff :
    PowerSeries.constantCoeff bellSquareEGF = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff, bellSquareEGF_coeff]
  rfl

theorem bellSquareEGF_hasSubst : PowerSeries.HasSubst bellSquareEGF :=
  PowerSeries.HasSubst.of_constantCoeff_zero' bellSquareEGF_constantCoeff

/-- The literal formal series log(1+A(z)); subtracting one reduces it
to substitution of A in the standard formal logarithm. -/
noncomputable def bellSquareLogSeries : PowerSeries ℚ :=
  PowerSeries.logOf (1 + bellSquareEGF)

theorem bellSquareLogSeries_eq :
    bellSquareLogSeries = (PowerSeries.log ℚ).subst bellSquareEGF := by
  rw [bellSquareLogSeries, PowerSeries.logOf_eq, add_sub_cancel_left]

theorem bellSquareEGF_coeff_pow_zero {n b : ℕ} (hnb : n < b) :
    PowerSeries.coeff n (bellSquareEGF ^ b) = 0 := by
  apply PowerSeries.coeff_of_lt_order
  exact (show (n : ℕ∞) < (b : ℕ∞) from ENat.coe_lt_coe.mpr hnb).trans_le
    (PowerSeries.le_order_pow_of_constantCoeff_eq_zero b bellSquareEGF_constantCoeff)

theorem bellSquareLog_term_support (n : ℕ) :
    Function.support (fun b : ℕ ↦
      PowerSeries.coeff b (PowerSeries.log ℚ) *
        PowerSeries.coeff n (bellSquareEGF ^ b)) ⊆
      (Finset.range (n + 1) : Set ℕ) := by
  intro b hb
  rw [Function.mem_support] at hb
  rw [Finset.mem_coe, Finset.mem_range]
  by_contra h
  have hnb : n < b := by omega
  exact hb (by rw [bellSquareEGF_coeff_pow_zero hnb, mul_zero])

/-- Every coefficient of the manuscript logarithm is a finite sum.
The zero and sign/denominator coefficients are those of the standard
formal log, not a separately defined combinatorial surrogate. -/
theorem bellSquareLogSeries_coeff (n : ℕ) :
    PowerSeries.coeff n bellSquareLogSeries =
      ∑ b ∈ Finset.range (n + 1),
        (if b = 0 then 0 else ((-1 : ℚ) ^ (b + 1) / b)) *
          PowerSeries.coeff n (bellSquareEGF ^ b) := by
  rw [bellSquareLogSeries_eq,
    PowerSeries.coeff_subst' bellSquareEGF_hasSubst (PowerSeries.log ℚ) n]
  change (∑ᶠ d : ℕ, PowerSeries.coeff d (PowerSeries.log ℚ) *
    PowerSeries.coeff n (bellSquareEGF ^ d)) = _
  rw [finsum_eq_finsetSum_of_support_subset _ (bellSquareLog_term_support n)]
  apply Finset.sum_congr rfl
  intro b _hb
  rw [PowerSeries.coeff_log]
  rfl

theorem bellSquareLogSeries_constantCoeff :
    PowerSeries.constantCoeff bellSquareLogSeries = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff, bellSquareLogSeries_coeff]
  norm_num

end BooleanAntichainsKernel
