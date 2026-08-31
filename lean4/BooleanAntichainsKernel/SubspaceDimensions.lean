import BooleanAntichainsKernel.SubspaceDecomposition
import Mathlib.LinearAlgebra.Dimension.DivisionRing
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

namespace BooleanAntichainsKernel

open Finset
open scoped Classical DirectSum

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable [FiniteDimensional K V] {k : ℕ}

namespace OrderedInternalDecomposition

theorem summand_finrank_ge_one (D : OrderedInternalDecomposition K V k) (i : Fin k) :
    1 ≤ Module.finrank K (D.1 i) :=
  Submodule.one_le_finrank_iff.mpr (D.2.2 i)

/-- Dimension is computed through the actual canonical direct-sum map. -/
theorem finrank_eq_sum (D : OrderedInternalDecomposition K V k) :
    Module.finrank K V = ∑ i, Module.finrank K (D.1 i) := by
  calc
    _ = Module.finrank K (⨁ i : Fin k, D.1 i) := D.sumLinearEquiv.finrank_eq.symm
    _ = _ := Module.finrank_directSum (R := K) (fun i : Fin k ↦ D.1 i)

theorem size_le_finrank (D : OrderedInternalDecomposition K V k) :
    k ≤ Module.finrank K V := by
  rw [D.finrank_eq_sum]
  have h : (∑ _i : Fin k, 1) ≤ ∑ i, Module.finrank K (D.1 i) :=
    Finset.sum_le_sum (fun i _ ↦ D.summand_finrank_ge_one i)
  simpa using h

end OrderedInternalDecomposition

/-- The paper's codimension d is the dimension of the genuine quotient. -/
theorem subspace_codimension_bounds (X : Submodule K V)
    (D : OrderedInternalDecomposition K (V ⧸ X) k) :
    k ≤ Module.finrank K (V ⧸ X) ∧ Module.finrank K (V ⧸ X) ≤ Module.finrank K V := by
  refine ⟨D.size_le_finrank, ?_⟩
  have h := Submodule.finrank_quotient_add_finrank (R := K) X
  omega

theorem subspace_codimension_profile (X : Submodule K V)
    (D : OrderedInternalDecomposition K (V ⧸ X) k) :
    (∀ i, 1 ≤ Module.finrank K (D.1 i)) ∧
    (∑ i, Module.finrank K (D.1 i)) = Module.finrank K (V ⧸ X) ∧
    k ≤ Module.finrank K (V ⧸ X) ∧ Module.finrank K (V ⧸ X) ≤ Module.finrank K V :=
  ⟨D.summand_finrank_ge_one, D.finrank_eq_sum.symm, subspace_codimension_bounds X D⟩

theorem standardSubspace_codimension_bounds {K : Type*} [Field K] (n k : ℕ)
    (X : Submodule K (Fin n → K))
    (D : OrderedInternalDecomposition K ((Fin n → K) ⧸ X) k) :
    k ≤ Module.finrank K ((Fin n → K) ⧸ X) ∧ Module.finrank K ((Fin n → K) ⧸ X) ≤ n := by
  simpa only [Module.finrank_fin_fun] using subspace_codimension_bounds X D

end BooleanAntichainsKernel
