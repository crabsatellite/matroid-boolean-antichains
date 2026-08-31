import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push
import Lean.Elab.Tactic.Omega

namespace BooleanAntichainsKernel

open scoped Classical

def partitionMobiusCandidate (b : ℕ) : ℤ :=
  if b = 0 then 0 else (-1 : ℤ) ^ (b - 1) * (b - 1).factorial

@[simp] theorem partitionMobiusCandidate_zero : partitionMobiusCandidate 0 = 0 := rfl

@[simp] theorem partitionMobiusCandidate_succ (k : ℕ) :
    partitionMobiusCandidate (k + 1) = (-1 : ℤ) ^ k * k.factorial := by
  simp [partitionMobiusCandidate]

theorem partitionMobiusCandidate_cancel (k : ℕ) :
    ((k + 1 : ℕ) : ℤ) * partitionMobiusCandidate (k + 1) +
      partitionMobiusCandidate (k + 2) = 0 := by
  rw [partitionMobiusCandidate_succ, partitionMobiusCandidate_succ]
  simp only [Nat.factorial_succ, Nat.cast_add, Nat.cast_one, pow_succ]
  push_cast
  ring

def partitionMobiusConvolution (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1),
    (Nat.stirlingSecond n k : ℤ) * partitionMobiusCandidate k

theorem partitionMobiusConvolution_one : partitionMobiusConvolution 1 = 1 := by
  norm_num [partitionMobiusConvolution, partitionMobiusCandidate,
    Nat.stirlingSecond, Finset.sum_range_succ]

theorem partitionMobiusConvolution_succ (n : ℕ) (hn : 1 ≤ n) :
    partitionMobiusConvolution (n + 1) = 0 := by
  rw [partitionMobiusConvolution, Finset.sum_range_succ']
  simp only [Nat.stirlingSecond_succ_zero, Nat.cast_zero, zero_mul]
  simp_rw [Nat.stirlingSecond_succ_succ, Nat.cast_add, Nat.cast_mul]
  simp_rw [add_mul, Finset.sum_add_distrib]
  let A : ℕ → ℤ := fun k ↦
    (((k + 1 : ℕ) : ℤ) * (Nat.stirlingSecond n (k + 1) : ℤ)) *
      partitionMobiusCandidate (k + 1)
  let D : ℕ → ℤ := fun k ↦
    (Nat.stirlingSecond n k : ℤ) * partitionMobiusCandidate (k + 1)
  rw [add_zero]
  change (∑ k ∈ Finset.range (n + 1), A k) + ∑ k ∈ Finset.range (n + 1), D k = 0
  rw [Finset.sum_range_succ, Finset.sum_range_succ']
  have hA : A n = 0 := by
    unfold A
    rw [Nat.stirlingSecond_eq_zero_of_lt (Nat.lt_succ_self n), Nat.cast_zero]
    simp
  have hD : D 0 = 0 := by
    unfold D
    rw [show n = (n - 1) + 1 by omega, Nat.stirlingSecond_succ_zero]
    simp
  simp only [hA, hD, add_zero]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro k hk
  unfold A D
  calc
    (((k + 1 : ℕ) : ℤ) * (Nat.stirlingSecond n (k + 1) : ℤ)) *
          partitionMobiusCandidate (k + 1) +
        (Nat.stirlingSecond n (k + 1) : ℤ) * partitionMobiusCandidate (k + 2) =
      (Nat.stirlingSecond n (k + 1) : ℤ) *
        (((k + 1 : ℕ) : ℤ) * partitionMobiusCandidate (k + 1) +
          partitionMobiusCandidate (k + 2)) := by ring
    _ = 0 := by rw [partitionMobiusCandidate_cancel, mul_zero]

end BooleanAntichainsKernel
