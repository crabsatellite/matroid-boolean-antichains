import BooleanAntichainsKernel.ProjectiveBasisCounting

namespace BooleanAntichainsKernel

open Finset
open scoped Classical

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable [FiniteDimensional K V] [Fintype V] {k : ℕ}

/-- Maximum Boolean antichains of the actual projective-subspace lattice
are in bijection with actual unordered independent projective-point sets. -/
noncomputable def projectiveAntichainEquivBasis (hk : k = Module.finrank K V) :
    BooleanAntichain k (Projectivization.Subspace K V) ≃ ProjectiveIndependentSet K V k :=
  ((projectiveAntichainEquiv k).trans (maximalSubspaceAntichainEquivInternal hk)).trans
    (projectiveBasisEquivInternal hk).symm

/-- The basis points are exactly the lines underlying the antichain's
erase/meet atoms; the actual lattice map is consumed here. -/
theorem projectiveAntichainEquivBasis_atoms (hk : k = Module.finrank K V)
    (C : BooleanAntichain k (Projectivization.Subspace K V)) :
    (projectiveAntichainEquivBasis hk C).1.image Projectivization.submodule =
      mapFamily projectiveSubspaceOrderIso (antichainAtoms C.1) := by
  change ((projectiveBasisEquivInternal hk).symm
    (maximalSubspaceAntichainEquivInternal hk (projectiveAntichainEquiv k C))).1.image
      Projectivization.submodule = _
  rw [projectiveBasisEquivInternal_symm_lines, maximalSubspaceAntichainEquivInternal_atoms,
    projectiveAntichainEquiv_atoms]

/-- The inverse returns the projective subspaces spanned by all-but-one
basis points, represented by the exact erase/join subspaces of V. -/
theorem projectiveAntichainEquivBasis_coatoms (hk : k = Module.finrank K V)
    (B : ProjectiveIndependentSet K V k) :
    ((projectiveAntichainEquivBasis hk).symm B).1 =
      mapFamily projectiveSubspaceOrderIso.symm
        (basisCoatoms (B.1.image Projectivization.submodule)) := by
  change mapFamily projectiveSubspaceOrderIso.symm
    (((maximalSubspaceAntichainEquivInternal hk).symm (projectiveBasisEquivInternal hk B)).1) = _
  rw [maximalSubspaceAntichainEquivInternal_coatoms, projectiveBasisEquivInternal_lines]

theorem projectiveAntichain_count_via_basis (hk : k = Module.finrank K V) :
    Fintype.card (BooleanAntichain k (Projectivization.Subspace K V)) =
      Fintype.card (ProjectiveIndependentSet K V k) :=
  Fintype.card_congr (projectiveAntichainEquivBasis hk)

/-- The displayed projective-count equation on the literal projective
geometry carrier, proved through its actual unordered bases. -/
theorem standardProjectiveAntichain_product (K : Type*) [Field K] [Fintype K]
    (r : ℕ) (hr : 1 ≤ r) :
    (Fintype.card (BooleanAntichain r (Projectivization.Subspace K (Fin r → K))) : ℚ) =
      (1 / (r.factorial : ℚ)) * ∏ i : Fin r,
        (((Fintype.card K : ℚ) ^ r - (Fintype.card K : ℚ) ^ i.1) /
          ((Fintype.card K : ℚ) - 1)) := by
  rw [projectiveAntichain_count_via_basis (by simp only [Module.finrank_fin_fun])]
  exact standardProjectiveBasis_product K r hr

end BooleanAntichainsKernel
