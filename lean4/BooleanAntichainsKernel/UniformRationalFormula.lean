import BooleanAntichainsKernel.UniformComputableFormula
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Nat.Cast.Field

namespace BooleanAntichainsKernel

open Finset
open scoped Classical

/-- The within-block and unused-element denominator divides the factorial,
as witnessed by the actual disjoint-block count on an N-element ground. -/
theorem blockProfile_denominator_dvd (N k : ℕ) (p : Fin k → ℕ) (hp : (∑ i, p i) ≤ N) :
    ((N - ∑ i, p i).factorial * ∏ i, (p i).factorial) ∣ N.factorial := by
  let A : Finset (Fin N) := univ
  have hm : Fintype.card (SizedDisjointBlocks A p) * (∏ i, (p i).factorial) =
      N.descFactorial (∑ i, p i) := by
    simpa only [A, Finset.card_univ, Fintype.card_fin] using
      (sizedDisjointBlocks_mul_factorials (A := A) (p := p))
  refine ⟨Fintype.card (SizedDisjointBlocks A p), ?_⟩
  calc
    _ = (N - ∑ i, p i).factorial * N.descFactorial (∑ i, p i) :=
      (Nat.factorial_mul_descFactorial hp).symm
    _ = (N - ∑ i, p i).factorial *
        (Fintype.card (SizedDisjointBlocks A p) * ∏ i, (p i).factorial) := by rw [← hm]
    _ = _ := by ac_rfl

theorem uniformProfileTerm_cast (n k b : ℕ) (p : Fin k → ℕ) (hp : (∑ i, p i) ≤ n - b) :
    (uniformProfileTerm n k b p : ℚ) =
      ((n - b).factorial : ℚ) /
        (((n - b - ∑ i, p i).factorial : ℚ) * ∏ i, ((p i).factorial : ℚ)) := by
  have hpos : 0 < (n - b - ∑ i, p i).factorial * ∏ i, (p i).factorial :=
    Nat.mul_pos (Nat.factorial_pos _) (Finset.prod_pos (fun i _ ↦ Nat.factorial_pos (p i)))
  unfold uniformProfileTerm
  rw [Nat.cast_div (blockProfile_denominator_dvd (n - b) k p hp)
    (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hpos)), Nat.cast_mul, Nat.cast_prod]

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem uniformProfileSum_factorial_dvd (E : Set α) (r k : ℕ)
    (hr : r ≤ E.ncard) (hk : 2 ≤ k) :
    k.factorial ∣
      ∑ b ∈ Finset.range r, E.ncard.choose b *
        ∑ p : UniformAdmissibleProfile E.ncard r k b,
          (E.ncard - b).factorial /
            ((E.ncard - b - ∑ i, p.1 i).factorial * ∏ i, (p.1 i).factorial) := by
  rw [← uniformBlockData_count_by_profile E r k, uniformBlockData_count hr hk]
  exact ⟨Fintype.card (BooleanAntichain k (MatroidFlat (uniformOn E r))), Nat.mul_comm _ _⟩

/-- Literal rational fractions in the paper's boxed equation. Both levels
of division are connected to the natural counts by proved divisibility and
nonzero factorial denominators. -/
theorem uniformOn_all_size_formula_rational (E : Set α) (r k : ℕ)
    (hr : r ≤ E.ncard) (hk : 2 ≤ k) :
    (Fintype.card (BooleanAntichain k (MatroidFlat (uniformOn E r))) : ℚ) =
      (1 / (k.factorial : ℚ)) *
        ∑ b ∈ Finset.range r, (E.ncard.choose b : ℚ) *
          ∑ p : UniformAdmissibleProfile E.ncard r k b,
            ((E.ncard - b).factorial : ℚ) /
              (((E.ncard - b - ∑ i, p.1 i).factorial : ℚ) * ∏ i, ((p.1 i).factorial : ℚ)) := by
  rw [uniformOn_all_size_formula E r k hr hk,
    Nat.cast_div (uniformProfileSum_factorial_dvd E r k hr hk)
      (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k))]
  simp only [Nat.cast_sum, Nat.cast_mul]
  conv_rhs => rw [one_div, mul_comm, ← div_eq_mul_inv]
  apply congrArg (fun z : ℚ ↦ z / (k.factorial : ℚ))
  apply Finset.sum_congr rfl
  intro b _
  apply congrArg (fun z : ℚ ↦ (E.ncard.choose b : ℚ) * z)
  apply Finset.sum_congr rfl
  intro p _
  exact uniformProfileTerm_cast E.ncard k b p.1 p.2.2.2.1

theorem uniform_all_size_formula_rational (n r k : ℕ) (hr : r ≤ n) (hk : 2 ≤ k) :
    (Fintype.card (BooleanAntichain k (MatroidFlat (uniformOn (Set.univ : Set (Fin n)) r))) : ℚ) =
      (1 / (k.factorial : ℚ)) *
        ∑ b ∈ Finset.range r, (n.choose b : ℚ) *
          ∑ p : UniformAdmissibleProfile n r k b,
            ((n - b).factorial : ℚ) /
              (((n - b - ∑ i, p.1 i).factorial : ℚ) * ∏ i, ((p.1 i).factorial : ℚ)) := by
  have hrE : r ≤ (Set.univ : Set (Fin n)).ncard := by
    simpa only [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] using hr
  let F (N : ℕ) : ℚ := (1 / (k.factorial : ℚ)) *
    ∑ b ∈ Finset.range r, (N.choose b : ℚ) *
      ∑ p : UniformAdmissibleProfile N r k b,
        ((N - b).factorial : ℚ) /
          (((N - b - ∑ i, p.1 i).factorial : ℚ) * ∏ i, ((p.1 i).factorial : ℚ))
  have hN : (Set.univ : Set (Fin n)).ncard = n := by
    simp only [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
  have h := uniformOn_all_size_formula_rational (Set.univ : Set (Fin n)) r k hrE hk
  change (Fintype.card (BooleanAntichain k (MatroidFlat (uniformOn (Set.univ : Set (Fin n)) r))) : ℚ) =
    F (Set.univ : Set (Fin n)).ncard at h
  exact h.trans (congrArg F hN)

end BooleanAntichainsKernel
