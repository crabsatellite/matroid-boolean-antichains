import BooleanAntichainsKernel.BasisWeightExpansion
import BooleanAntichainsKernel.SpanAtoms

namespace BooleanAntichainsKernel

open Finset

variable {α : Type*} [Fintype α]

/-- Equation `eq:weighted` on the actual atoms of the actual Boolean span. -/
theorem weighted_basis_polynomial (M : Matroid α) :
    matroidBasisPolynomial M =
      ∑ C : MaximumBooleanAntichain M,
        ∏ A ∈ spanAtomFinset C.1, ∑ e ∈ parallelClassElements A,
          (MvPolynomial.X e : MvPolynomial α ℤ) := by
  have hats (C : MaximumBooleanAntichain M) : spanAtomFinset C.1 = antichainAtoms C.1 :=
    spanAtomFinset_eq_antichainAtoms C.1 C.2.2
  simp_rw [hats]
  exact basis_polynomial_reconstructed_atoms M

/-- Equation `eq:weighted-count`, derived by setting every variable to one. -/
theorem weighted_basis_count (M : Matroid α) :
    Fintype.card (MatroidBases M) =
      ∑ C : MaximumBooleanAntichain M,
        ∏ A ∈ spanAtomFinset C.1, (parallelClassElements A).card := by
  have hats (C : MaximumBooleanAntichain M) : spanAtomFinset C.1 = antichainAtoms C.1 :=
    spanAtomFinset_eq_antichainAtoms C.1 C.2.2
  simp_rw [hats]
  exact basis_count_reconstructed_atoms M

end BooleanAntichainsKernel
