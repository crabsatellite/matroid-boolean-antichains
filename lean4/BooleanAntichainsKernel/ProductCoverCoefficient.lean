import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Rat.Cast.Order

namespace BooleanAntichainsKernel

/-- The number of active covers is the paper's exact multinomial coefficient,
written without division until positivity of the denominator is available. -/
theorem cover_choose_mul_factorials {k a b : ℕ}
    (ha : a ≤ k) (hb : b ≤ k) (hab : k ≤ a + b) :
    k.choose a * a.choose (k - b) *
      ((k - a).factorial * (k - b).factorial * (a + b - k).factorial) = k.factorial := by
  have hkb : k - b ≤ a := by omega
  have hsub : a - (k - b) = a + b - k := by omega
  have hsecond := Nat.choose_mul_factorial_mul_factorial hkb
  rw [hsub] at hsecond
  calc
    _ = k.choose a *
        (a.choose (k - b) * (k - b).factorial * (a + b - k).factorial) *
          (k - a).factorial := by ac_rfl
    _ = k.factorial := by rw [hsecond, Nat.choose_mul_factorial_mul_factorial ha]

lemma factorial_cast_ne_zero (n : ℕ) : (n.factorial : ℚ) ≠ 0 :=
  Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)

/-- Divide the labelled cover contribution by k!, with exactly the
factorials and summation boundary displayed in eq:product-convolution. -/
theorem normalized_cover_coefficient {k a b : ℕ} (ha : a ≤ k) (hb : b ≤ k) :
    ((k.choose a : ℚ) * (a.choose (k - b) : ℚ) *
      (a.factorial : ℚ) * (b.factorial : ℚ)) / (k.factorial : ℚ) =
      if k ≤ a + b then
        (a.factorial : ℚ) * (b.factorial : ℚ) /
          ((k - a).factorial * (k - b).factorial * (a + b - k).factorial : ℚ)
      else 0 := by
  by_cases hab : k ≤ a + b
  · rw [if_pos hab]
    have hmul :
        (k.choose a : ℚ) * (a.choose (k - b) : ℚ) *
          ((k - a).factorial * (k - b).factorial * (a + b - k).factorial : ℚ) =
        (k.factorial : ℚ) := by
      exact_mod_cast cover_choose_mul_factorials ha hb hab
    have hden : ((k - a).factorial * (k - b).factorial *
        (a + b - k).factorial : ℚ) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (factorial_cast_ne_zero _) (factorial_cast_ne_zero _))
        (factorial_cast_ne_zero _)
    apply (div_eq_div_iff (factorial_cast_ne_zero k) hden).mpr
    calc
      _ = ((k.choose a : ℚ) * (a.choose (k - b) : ℚ) *
            ((k - a).factorial * (k - b).factorial * (a + b - k).factorial : ℚ)) *
          (a.factorial : ℚ) * (b.factorial : ℚ) := by ac_rfl
      _ = (a.factorial : ℚ) * (b.factorial : ℚ) * (k.factorial : ℚ) := by
        rw [hmul]
        ac_rfl
  · have hzero : a.choose (k - b) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    simp [hab, hzero]

end BooleanAntichainsKernel
