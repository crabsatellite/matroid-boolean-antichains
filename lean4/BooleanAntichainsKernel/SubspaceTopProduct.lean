import BooleanAntichainsKernel.SubspaceGaussianFormula

namespace BooleanAntichainsKernel

open Finset
open scoped Classical

theorem positiveDimensionProfile_diagonal {n : ℕ} (p : PositiveDimensionProfile n n)
    (i : Fin n) : p.1 i = 1 := by
  have hs : (∑ _j : Fin n, 1) = ∑ j, p.1 j := by simp [p.2.2]
  exact ((sum_eq_sum_iff_of_le (fun j _ ↦ p.2.1 j)).mp hs i (mem_univ i)).symm

def diagonalDimensionProfile (n : ℕ) : PositiveDimensionProfile n n :=
  ⟨fun _ ↦ 1, fun _ ↦ le_rfl, by simp⟩

instance (n : ℕ) : Unique (PositiveDimensionProfile n n) where
  default := diagonalDimensionProfile n
  uniq p := Subtype.ext (funext fun i ↦ positiveDimensionProfile_diagonal p i)

theorem generalLinearCard_one (K : Type*) [Field K] [Fintype K] :
    generalLinearCard K 1 = Fintype.card K - 1 := by
  rw [generalLinearCard_product]
  simp

theorem gaussianCoefficient_diagonal (K : Type*) [Field K] [Fintype K] (n : ℕ) :
    gaussianCoefficient (Fintype.card K) n n = 1 := by
  rw [gaussianCoefficient, frameProduct_diagonal]
  exact div_self (Nat.cast_ne_zero.mpr (Nat.ne_of_gt (generalLinearCard_pos K n)))

/-- At k=d there is exactly one positive dimension profile: every
summand is a line. The original k! normalization is retained. -/
theorem directSumProfileCount_diagonal (K : Type*) [Field K] [Fintype K] (n : ℕ) :
    directSumProfileCount K n n = (1 / (n.factorial : ℚ)) *
      ∏ i : Fin n, (((Fintype.card K) ^ n - (Fintype.card K) ^ i.1 : ℕ) : ℚ) /
        ((Fintype.card K - 1 : ℕ) : ℚ) := by
  rw [directSumProfileCount, Fintype.sum_unique]
  change (1 / (n.factorial : ℚ)) *
    ((generalLinearCard K n : ℚ) / ∏ _i : Fin n, (generalLinearCard K 1 : ℚ)) = _
  rw [prod_div_distrib, generalLinearCard_one, generalLinearCard_product K n, Nat.cast_prod]

/-- The subspace theorem's top layer reduces to the displayed
projective-basis product, with rational subtraction and no truncated terms. -/
theorem standardSubspace_top_product (K : Type*) [Field K] [Fintype K]
    (n : ℕ) (hn : 1 ≤ n) :
    (Fintype.card (BooleanAntichain n (Submodule K (Fin n → K))) : ℚ) =
      (1 / (n.factorial : ℚ)) * ∏ i : Fin n,
        (((Fintype.card K : ℚ) ^ n - (Fintype.card K : ℚ) ^ i.1) /
          ((Fintype.card K : ℚ) - 1)) := by
  rw [standardSubspace_all_size_formula K n n hn, Icc_self, sum_singleton,
    gaussianCoefficient_diagonal, one_mul, directSumProfileCount_diagonal]
  apply congrArg (fun z : ℚ ↦ (1 / (n.factorial : ℚ)) * z)
  apply prod_congr rfl
  intro i _
  rw [Nat.cast_sub (Nat.pow_le_pow_right (Fintype.card_pos (α := K)) i.2.le),
    Nat.cast_pow, Nat.cast_pow, Nat.cast_sub (Fintype.one_lt_card (α := K)).le, Nat.cast_one]

end BooleanAntichainsKernel
