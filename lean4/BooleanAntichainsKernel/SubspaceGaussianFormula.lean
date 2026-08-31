import BooleanAntichainsKernel.GaussianSubspaceCount
import BooleanAntichainsKernel.SubspaceDirectSumFormula
import Mathlib.Order.Interval.Finset.Nat

namespace BooleanAntichainsKernel

open Finset
open scoped Classical

variable {K V : Type*} [Field K] [Fintype K] [AddCommGroup V] [Module K V]
variable [Fintype V] [FiniteDimensional K V]

/-- Group a function of the actual quotient dimension by the proved
Gaussian cardinalities of its codimension fibres. -/
theorem quotientDimension_sum (f : ℕ → ℚ) :
    (∑ X : Submodule K V, f (Module.finrank K (V ⧸ X))) =
      ∑ d ∈ Icc 0 (Module.finrank K V),
        gaussianCoefficient (Fintype.card K) (Module.finrank K V) d * f d := by
  have hb : ∀ X ∈ (univ : Finset (Submodule K V)),
      Module.finrank K (V ⧸ X) ∈ Icc 0 (Module.finrank K V) := by
    intro X _
    have h := Submodule.finrank_quotient_add_finrank (R := K) X
    exact mem_Icc.mpr ⟨Nat.zero_le _, by omega⟩
  rw [← sum_fiberwise_of_maps_to' hb f]
  apply sum_congr rfl
  intro d hd
  have hc : (univ.filter (fun X : Submodule K V ↦ Module.finrank K (V ⧸ X) = d)).card =
      Fintype.card (CodimensionSubspace K V d) :=
    (Fintype.card_subtype (fun X : Submodule K V ↦ Module.finrank K (V ⧸ X) = d)).symm
  simp only [sum_const, nsmul_eq_mul, hc]
  rw [codimensionSubspace_gaussian (mem_Icc.mp hd).2]

/-- The paper's displayed Gaussian sum, with the lower limit k earned by
nonzero summand dimensions and with both genuine counting bridges consumed. -/
theorem subspace_all_size_formula (k : ℕ) (_hk : 1 ≤ k) :
    (Fintype.card (BooleanAntichain k (Submodule K V)) : ℚ) =
      ∑ d ∈ Icc k (Module.finrank K V),
        gaussianCoefficient (Fintype.card K) (Module.finrank K V) d *
          directSumProfileCount K d k := by
  rw [subspace_count_by_directSumProfiles,
    quotientDimension_sum (K := K) (V := V) (fun d ↦ directSumProfileCount K d k)]
  symm
  apply sum_subset
  · intro d hd
    exact mem_Icc.mpr ⟨Nat.zero_le _, (mem_Icc.mp hd).2⟩
  · intro d hd hnot
    have hd' := mem_Icc.mp hd
    have hdk : d < k := by
      simp only [mem_Icc, not_and_or, not_le] at hnot
      omega
    rw [directSumProfileCount_zero_of_lt K hdk, mul_zero]

theorem standardSubspace_all_size_formula (K : Type*) [Field K] [Fintype K]
    (n k : ℕ) (hk : 1 ≤ k) :
    (Fintype.card (BooleanAntichain k (Submodule K (Fin n → K))) : ℚ) =
      ∑ d ∈ Icc k n,
        gaussianCoefficient (Fintype.card K) n d * directSumProfileCount K d k := by
  simpa only [Module.finrank_fin_fun] using
    (subspace_all_size_formula (K := K) (V := Fin n → K) k hk)

end BooleanAntichainsKernel
