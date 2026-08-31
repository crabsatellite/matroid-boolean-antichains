import BooleanAntichainsKernel.BooleanBaseCounts
import BooleanAntichainsKernel.ProductLabelledCounting

namespace BooleanAntichainsKernel

open Finset
open scoped Classical

lemma sum_booleanOne_labelled_layer (k a u : ℕ) :
    (∑ b ∈ range (k + 2), (k + 1).choose a * a.choose (k + 1 - b) * u *
      (b.factorial * (if b ≤ 1 then 1 else 0))) =
    (k + 1).choose a * a.choose (k + 1) * u +
      (k + 1).choose a * a.choose k * u := by
  calc
    _ = ∑ b ∈ range 2, (k + 1).choose a * a.choose (k + 1 - b) * u *
        (b.factorial * (if b ≤ 1 then 1 else 0)) :=
      Finset.eventually_constant_sum (N := 2)
        (fun b hb ↦ by rw [if_neg (by omega)]; simp) (by omega)
    _ = _ := by simp [Finset.sum_range_succ]

/-- Exact specialization of the covering-active-set sum to B1. -/
theorem sum_product_with_booleanOne (k : ℕ) (u : ℕ → ℕ) :
    (∑ a ∈ range (k + 2), ∑ b ∈ range (k + 2),
      (k + 1).choose a * a.choose (k + 1 - b) * u a *
        (b.factorial * (if b ≤ 1 then 1 else 0))) =
      (k + 2) * u (k + 1) + (k + 1) * u k := by
  simp_rw [sum_booleanOne_labelled_layer]
  rw [Finset.sum_add_distrib]
  have hfirst :
      (∑ a ∈ range (k + 2), (k + 1).choose a * a.choose (k + 1) * u a) = u (k + 1) := by
    rw [Finset.sum_eq_single (k + 1)]
    · simp
    · intro a ha hne
      have hlt : a < k + 1 := by have := Finset.mem_range.mp ha; omega
      rw [Nat.choose_eq_zero_of_lt hlt]
      simp
    · intro hnot
      exact (hnot (Finset.mem_range.mpr (by omega))).elim
  have hsecond :
      (∑ a ∈ range (k + 2), (k + 1).choose a * a.choose k * u a) =
        (k + 1) * u k + (k + 1) * u (k + 1) := by
    rw [Finset.sum_range_succ]
    have hlow :
        (∑ a ∈ range (k + 1), (k + 1).choose a * a.choose k * u a) = (k + 1) * u k := by
      rw [Finset.sum_eq_single k]
      · simp [Nat.choose_succ_self_right]
      · intro a ha hne
        have hlt : a < k := by have := Finset.mem_range.mp ha; omega
        rw [Nat.choose_eq_zero_of_lt hlt]
        simp
      · intro hnot
        exact (hnot (Finset.mem_range.mpr (by omega))).elim
    rw [hlow]
    simp [Nat.choose_succ_self_right]
  rw [hfirst, hsecond]
  simp only [Nat.add_mul, Nat.one_mul]
  omega

variable {L : Type*} [Fintype L] [DecidableEq L] [Lattice L] [OrderBot L] [OrderTop L]

/-- The manuscript recurrence after the product theorem, with k+1 as the
positive size so that no negative index is represented by truncated subtraction. -/
theorem product_booleanOne_recurrence (k : ℕ) :
    Fintype.card (BooleanAntichain (k + 1) (L × Finset (Fin 1))) =
      (k + 2) * Fintype.card (BooleanAntichain (k + 1) L) +
        Fintype.card (BooleanAntichain k L) := by
  have hc := productEmbedding_count_by_sizes (L := L) (K := Finset (Fin 1)) (k + 1)
  rw [topBooleanEmbedding_count] at hc
  simp_rw [booleanOne_count] at hc
  rw [sum_product_with_booleanOne] at hc
  apply Nat.eq_of_mul_eq_mul_right (Nat.factorial_pos (k + 1))
  calc
    _ = (k + 2) * ((k + 1).factorial * Fintype.card (BooleanAntichain (k + 1) L)) +
          (k + 1) * (k.factorial * Fintype.card (BooleanAntichain k L)) := hc
    _ = _ := by
      conv_rhs => rw [Nat.add_mul]
      apply congrArg₂ (· + ·)
      · ac_rfl
      · rw [Nat.factorial_succ]
        ac_rfl

end BooleanAntichainsKernel
