import BooleanAntichainsKernel.SubspaceAntichainFibres
import BooleanAntichainsKernel.UnorderedInternalBijection

namespace BooleanAntichainsKernel

open Finset
open scoped Classical

variable {R V : Type*} [Ring R] [AddCommGroup V] [Module R V] [Fintype V]

/-- The paper's genuine unordered correspondence, indexed by the actual
common intersection and using actual summand subspaces of its quotient. -/
noncomputable def subspaceUnorderedSigmaEquiv (k : ℕ) :
    (Σ X : Submodule R V, UnorderedInternalDecomposition R (V ⧸ X) k) ≃
      BooleanAntichain k (Submodule R V) :=
  (Equiv.sigmaCongrRight fun X ↦
    (bottomAntichainEquivUnorderedInternal (R := R) (V := V ⧸ X) (k := k)).symm.trans
      (subspaceAntichainFibreEquivQuotient X).symm).trans
    booleanAntichainBottomSigmaEquiv

@[simp] theorem subspaceUnorderedSigmaEquiv_symm_index {k : ℕ}
    (C : BooleanAntichain k (Submodule R V)) :
    ((subspaceUnorderedSigmaEquiv k).symm C).1 = C.1.inf id := rfl

/-- The forward summands are exactly the images A/X of the original
erase/meet atoms, not an equinumerous family in another quotient. -/
theorem subspaceUnorderedSigmaEquiv_atoms {k : ℕ}
    (C : BooleanAntichain k (Submodule R V)) :
    ((subspaceUnorderedSigmaEquiv k).symm C).2.1 =
      (antichainAtoms C.1).image (fun A ↦ A.map (C.1.inf id).mkQ) := by
  change (bottomAntichainToUnorderedInternal
    (subspaceAntichainFibreEquivQuotient (C.1.inf id) ⟨C, rfl⟩)).1 = _
  rw [bottomAntichainToUnorderedInternal_val]
  exact subspaceAntichainFibre_atoms (C.1.inf id) ⟨C, rfl⟩

theorem subspaceUnorderedSigmaEquiv_coatoms {k : ℕ} (X : Submodule R V)
    (D : UnorderedInternalDecomposition R (V ⧸ X) k) :
    (subspaceUnorderedSigmaEquiv k ⟨X, D⟩).1 =
      (basisCoatoms D.1).image (fun H ↦ H.comap X.mkQ) := by
  calc
    _ = (unorderedInternalToBottomAntichain D).1.1.image (fun H ↦ H.comap X.mkQ) :=
      subspaceAntichainFibreEquivQuotient_symm_val X (unorderedInternalToBottomAntichain D)
    _ = _ := congrArg (fun A : Finset (Submodule R (V ⧸ X)) ↦
      A.image (fun H ↦ H.comap X.mkQ)) (unorderedInternalToBottomAntichain_val D)

/-- The inverse is the literal coatom formula in the manuscript. -/
theorem subspaceUnorderedSigmaEquiv_coatom_formula {k : ℕ} (X : Submodule R V)
    (D : UnorderedInternalDecomposition R (V ⧸ X) k) :
    (subspaceUnorderedSigmaEquiv k ⟨X, D⟩).1 =
      D.1.image (fun U ↦ ((D.1.erase U).sup id).comap X.mkQ) := by
  rw [subspaceUnorderedSigmaEquiv_coatoms, basisCoatoms, Finset.image_image]
  rfl

theorem subspace_count_by_unordered_quotients (k : ℕ) :
    Fintype.card (BooleanAntichain k (Submodule R V)) =
      ∑ X : Submodule R V, Fintype.card (UnorderedInternalDecomposition R (V ⧸ X) k) := by
  rw [← Fintype.card_congr (subspaceUnorderedSigmaEquiv (R := R) (V := V) k), Fintype.card_sigma]

theorem standardSubspace_unordered_codimension_bounds {K : Type*} [Field K] (n k : ℕ)
    (X : Submodule K (Fin n → K))
    (D : UnorderedInternalDecomposition K ((Fin n → K) ⧸ X) k) :
    k ≤ Module.finrank K ((Fin n → K) ⧸ X) ∧ Module.finrank K ((Fin n → K) ⧸ X) ≤ n :=
  standardSubspace_codimension_bounds n k X (orderUnorderedInternal D)

end BooleanAntichainsKernel
