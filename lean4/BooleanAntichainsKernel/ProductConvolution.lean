import BooleanAntichainsKernel.ProductLabelledCounting
import BooleanAntichainsKernel.ProductCoverCoefficient
import Mathlib.Algebra.BigOperators.Field

namespace BooleanAntichainsKernel

open Finset
open scoped Classical

variable {L K : Type*}
variable [Fintype L] [DecidableEq L] [Lattice L] [OrderBot L] [OrderTop L]
variable [Fintype K] [DecidableEq K] [Lattice K] [OrderBot K] [OrderTop K]

/-- The explicit positive convolution in eq:product-convolution. Its proof
counts the genuine covering active sets and divides labelled embeddings by
the proved factorial fibres. Rational division retains the displayed
factorial ratio, including all zero-dimensional boundary cases. -/
theorem productAntichain_count_convolution (k : ℕ) :
    (Fintype.card (BooleanAntichain k (L × K)) : ℚ) =
      ∑ a ∈ range (k + 1), ∑ b ∈ (range (k + 1)).filter (fun b ↦ k ≤ a + b),
        ((a.factorial : ℚ) * (b.factorial : ℚ) /
          ((k - a).factorial * (k - b).factorial * (a + b - k).factorial : ℚ)) *
          (Fintype.card (BooleanAntichain a L) : ℚ) *
          (Fintype.card (BooleanAntichain b K) : ℚ) := by
  calc
    _ = (Fintype.card (TopBooleanEmbedding (Fin k) (L × K)) : ℚ) / (k.factorial : ℚ) := by
      rw [topBooleanEmbedding_count, Nat.cast_mul, mul_div_cancel_right₀ _ (factorial_cast_ne_zero k)]
    _ = (∑ a ∈ range (k + 1), ∑ b ∈ range (k + 1),
        (k.choose a : ℚ) * (a.choose (k - b) : ℚ) *
          ((a.factorial : ℚ) * (Fintype.card (BooleanAntichain a L) : ℚ)) *
          ((b.factorial : ℚ) * (Fintype.card (BooleanAntichain b K) : ℚ))) /
            (k.factorial : ℚ) := by
      rw [productEmbedding_count_by_sizes]
      simp only [Nat.cast_sum, Nat.cast_mul]
    _ = ∑ a ∈ range (k + 1), ∑ b ∈ range (k + 1),
        (((k.choose a : ℚ) * (a.choose (k - b) : ℚ) *
          (a.factorial : ℚ) * (b.factorial : ℚ)) / (k.factorial : ℚ)) *
          (Fintype.card (BooleanAntichain a L) : ℚ) *
          (Fintype.card (BooleanAntichain b K) : ℚ) := by
      simp only [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      simp only [div_eq_mul_inv]
      ac_rfl
    _ = ∑ a ∈ range (k + 1), ∑ b ∈ range (k + 1),
        if k ≤ a + b then
          ((a.factorial : ℚ) * (b.factorial : ℚ) /
            ((k - a).factorial * (k - b).factorial * (a + b - k).factorial : ℚ)) *
            (Fintype.card (BooleanAntichain a L) : ℚ) *
            (Fintype.card (BooleanAntichain b K) : ℚ)
        else 0 := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      rw [normalized_cover_coefficient
        (Nat.le_of_lt_succ (Finset.mem_range.mp ha))
        (Nat.le_of_lt_succ (Finset.mem_range.mp hb))]
      split_ifs <;> simp
    _ = _ := by
      simp only [Finset.sum_filter]

end BooleanAntichainsKernel
