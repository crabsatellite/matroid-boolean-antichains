import BooleanAntichainsKernel.SubspaceGaussianFormula

namespace BooleanAntichainsKernel

open Finset

abbrev BoundedPositiveDimensionProfile (d k : ℕ) :=
  {p : Fin k → Fin (d + 1) // (∀ i, 1 ≤ (p i).1) ∧ (∑ i, (p i).1) = d}

instance (d k : ℕ) : Fintype (BoundedPositiveDimensionProfile d k) := Subtype.fintype _

/-- Exact bounded encoding of the natural positive dimension variables. -/
def positiveDimensionEquivBounded (d k : ℕ) :
    PositiveDimensionProfile d k ≃ BoundedPositiveDimensionProfile d k where
  toFun p := ⟨positiveDimensionCode p, p.2⟩
  invFun p := ⟨fun i ↦ (p.1 i).1, p.2⟩
  left_inv _ := Subtype.ext (funext fun _ ↦ rfl)
  right_inv _ := Subtype.ext (funext fun _ ↦ Fin.ext rfl)

def directSumBoundedCount (q d k : ℕ) : ℚ :=
  (1 / (k.factorial : ℚ)) * ∑ p : Fin k → Fin (d + 1),
    if (∀ i, 1 ≤ (p i).1) ∧ (∑ i, (p i).1) = d then
      (frameProduct q d d : ℚ) / ∏ i, (frameProduct q (p i).1 (p i).1 : ℚ)
    else 0

theorem positiveDimension_sum_eq_bounded (d k : ℕ) (f : (Fin k → ℕ) → ℚ) :
    (∑ p : PositiveDimensionProfile d k, f p.1) =
      ∑ p : Fin k → Fin (d + 1),
        if (∀ i, 1 ≤ (p i).1) ∧ (∑ i, (p i).1) = d then f (fun i ↦ (p i).1) else 0 := by
  calc
    _ = ∑ p : BoundedPositiveDimensionProfile d k, f (fun i ↦ (p.1 i).1) :=
      Fintype.sum_equiv (positiveDimensionEquivBounded d k) _ _ (fun _ ↦ rfl)
    _ = ∑ p ∈ (univ : Finset (Fin k → Fin (d + 1))).filter
          (fun p ↦ (∀ i, 1 ≤ (p i).1) ∧ (∑ i, (p i).1) = d),
          f (fun i ↦ (p i).1) :=
      (Finset.sum_subtype
        (p := fun p : Fin k → Fin (d + 1) ↦ (∀ i, 1 ≤ (p i).1) ∧ (∑ i, (p i).1) = d)
        (F := (inferInstance : Fintype (BoundedPositiveDimensionProfile d k)))
        _ (fun _ ↦ by simp only [mem_filter, mem_univ, true_and])
        (fun p ↦ f (fun i ↦ (p i).1))).symm
    _ = _ := by rw [sum_filter]

/-- Kernel evaluation uses the literal GL product and a proved bijection
on dimension profiles, not an external numerical certificate. -/
theorem directSumProfileCount_eq_bounded (K : Type*) [Field K] [Fintype K] (d k : ℕ) :
    directSumProfileCount K d k = directSumBoundedCount (Fintype.card K) d k := by
  unfold directSumProfileCount directSumBoundedCount
  simp_rw [← frameProduct_diagonal]
  rw [positiveDimension_sum_eq_bounded d k
    (fun p ↦ (frameProduct (Fintype.card K) d d : ℚ) /
      ∏ i, (frameProduct (Fintype.card K) (p i) (p i) : ℚ))]

def finiteSubspaceEnumerator (q n k : ℕ) : ℚ :=
  ∑ d ∈ Icc k n, gaussianCoefficient q n d * directSumBoundedCount q d k

theorem subspace_count_eq_bounded (K : Type*) [Field K] [Fintype K]
    (n k : ℕ) (hk : 1 ≤ k) :
    (Fintype.card (BooleanAntichain k (Submodule K (Fin n → K))) : ℚ) =
      finiteSubspaceEnumerator (Fintype.card K) n k := by
  rw [standardSubspace_all_size_formula K n k hk]
  simp_rw [directSumProfileCount_eq_bounded]
  rfl

end BooleanAntichainsKernel
