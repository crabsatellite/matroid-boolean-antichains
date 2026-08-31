import BooleanAntichainsKernel.InternalDimensionProfiles
import BooleanAntichainsKernel.SubspaceUnorderedCorrespondence

namespace BooleanAntichainsKernel

open Finset
open scoped Classical

lemma positiveDimensionProfile_size_le {d k : ℕ} (p : PositiveDimensionProfile d k) : k ≤ d := by
  have h : (∑ _i : Fin k, 1) ≤ ∑ i, p.1 i := Finset.sum_le_sum (fun i _ ↦ p.2.1 i)
  simpa [p.2.2] using h

theorem directSumProfileCount_zero_of_lt (K : Type*) [Field K] [Fintype K]
    {d k : ℕ} (hdk : d < k) : directSumProfileCount K d k = 0 := by
  letI : IsEmpty (PositiveDimensionProfile d k) :=
    ⟨fun p ↦ hdk.not_ge (positiveDimensionProfile_size_le p)⟩
  simp [directSumProfileCount]

theorem standardInternal_count_by_dimensions (K : Type*) [Field K] [Fintype K] (d k : ℕ) :
    (Fintype.card (UnorderedInternalDecomposition K (Fin d → K) k) : ℚ) =
      directSumProfileCount K d k := by
  simpa only [Module.finrank_fin_fun] using
    (unorderedInternal_count_by_dimensions (K := K) (V := Fin d → K) (k := k))

variable {K V : Type*} [Field K] [Fintype K] [AddCommGroup V] [Module K V]
variable [Fintype V] [FiniteDimensional K V]

/-- Consume the GL/profile count for each genuine quotient in the
unordered correspondence. The Gaussian grouping of these X remains
a separate producer, not an assumed identification. -/
theorem subspace_count_by_directSumProfiles (k : ℕ) :
    (Fintype.card (BooleanAntichain k (Submodule K V)) : ℚ) =
      ∑ X : Submodule K V, directSumProfileCount K (Module.finrank K (V ⧸ X)) k := by
  rw [subspace_count_by_unordered_quotients, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro X _
  exact unorderedInternal_count_by_dimensions (K := K) (V := V ⧸ X) (k := k)

end BooleanAntichainsKernel
