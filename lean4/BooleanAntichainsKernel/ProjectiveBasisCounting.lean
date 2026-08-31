import BooleanAntichainsKernel.ProjectiveIndependentSets

namespace BooleanAntichainsKernel

open Finset
open scoped Classical

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable [FiniteDimensional K V] [Fintype V] {k : ℕ}

/-- The actual line-set and frame bijections consume the already proved
enumeration fibres; k! is not built into the unordered basis carrier. -/
theorem projectiveBasis_labelling_count (hk : k = Module.finrank K V) :
    Fintype.card (OrderedProjectiveFrame K V k) =
      Fintype.card (ProjectiveIndependentSet K V k) * k.factorial := by
  rw [Fintype.card_congr (orderedProjectiveEquivInternal hk),
    orderedInternal_count_eq_unordered_mul_factorial,
    ← Fintype.card_congr (projectiveBasisEquivInternal hk)]

theorem projectiveBasis_count_by_frames (hk : k = Module.finrank K V) :
    (Fintype.card (ProjectiveIndependentSet K V k) : ℚ) =
      (Fintype.card (OrderedProjectiveFrame K V k) : ℚ) / (k.factorial : ℚ) := by
  apply (eq_div_iff (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k))).mpr
  exact_mod_cast (projectiveBasis_labelling_count (K := K) (V := V) hk).symm

variable [Fintype K]

/-- Count the literal unordered independent projective points through
vector frames, their nonzero-scalar fibres, and their labellings. -/
theorem projectiveBasis_product_natCast (hk : k = Module.finrank K V) :
    (Fintype.card (ProjectiveIndependentSet K V k) : ℚ) =
      (1 / (k.factorial : ℚ)) * ∏ i : Fin k,
        (((Fintype.card K) ^ k - (Fintype.card K) ^ i.1 : ℕ) : ℚ) /
          ((Fintype.card K - 1 : ℕ) : ℚ) := by
  rw [projectiveBasis_count_by_frames hk, projectiveFrame_count_rational hk.le, ← hk,
    prod_div_distrib, prod_const, card_univ, Fintype.card_fin]
  simp only [frameProduct, Nat.cast_prod, div_eq_mul_inv, one_mul]
  ac_rfl

theorem projectiveBasis_product (hk : k = Module.finrank K V) :
    (Fintype.card (ProjectiveIndependentSet K V k) : ℚ) =
      (1 / (k.factorial : ℚ)) * ∏ i : Fin k,
        (((Fintype.card K : ℚ) ^ k - (Fintype.card K : ℚ) ^ i.1) /
          ((Fintype.card K : ℚ) - 1)) := by
  rw [projectiveBasis_product_natCast hk]
  apply congrArg (fun z : ℚ ↦ (1 / (k.factorial : ℚ)) * z)
  apply prod_congr rfl
  intro i _
  rw [Nat.cast_sub (Nat.pow_le_pow_right (Fintype.card_pos (α := K)) i.2.le),
    Nat.cast_pow, Nat.cast_pow, Nat.cast_sub (Fintype.one_lt_card (α := K)).le, Nat.cast_one]

theorem standardProjectiveBasis_product (K : Type*) [Field K] [Fintype K]
    (r : ℕ) (_hr : 1 ≤ r) :
    (Fintype.card (ProjectiveIndependentSet K (Fin r → K) r) : ℚ) =
      (1 / (r.factorial : ℚ)) * ∏ i : Fin r,
        (((Fintype.card K : ℚ) ^ r - (Fintype.card K : ℚ) ^ i.1) /
          ((Fintype.card K : ℚ) - 1)) :=
  projectiveBasis_product (by simp only [Module.finrank_fin_fun])

end BooleanAntichainsKernel
