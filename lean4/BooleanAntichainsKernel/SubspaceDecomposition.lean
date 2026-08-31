import BooleanAntichainsKernel.InternalSumAtoms

namespace BooleanAntichainsKernel

open Finset
open scoped Classical DirectSum

variable {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]

/-- Labelled Boolean embeddings are classified by their literal bottom and
the actual nonzero internal direct-sum decomposition of its quotient. -/
def subspaceInternalSigmaEquiv (k : ℕ) :
    (Σ X : Submodule R V, OrderedInternalDecomposition R (V ⧸ X) k) ≃
      TopBooleanEmbedding (Fin k) (Submodule R V) :=
  (Equiv.sigmaCongrRight fun X ↦
    (bottomEmbeddingEquivInternal (R := R) (V := V ⧸ X) (k := k)).symm).trans
    subspaceQuotientSigmaEquiv

@[simp] theorem subspaceInternalSigmaEquiv_apply {k : ℕ} (X : Submodule R V)
    (D : OrderedInternalDecomposition R (V ⧸ X) k) (S : Finset (Fin k)) :
    (subspaceInternalSigmaEquiv k ⟨X, D⟩).1.1 S = (S.sup D.1).comap X.mkQ := rfl

@[simp] theorem subspaceInternalSigmaEquiv_symm_index {k : ℕ}
    (f : TopBooleanEmbedding (Fin k) (Submodule R V)) :
    ((subspaceInternalSigmaEquiv k).symm f).1 = f.1.1 ∅ := rfl

theorem subspaceInternalSigmaEquiv_commonMeet {k : ℕ} (X : Submodule R V)
    (D : OrderedInternalDecomposition R (V ⧸ X) k) :
    Finset.univ.inf (topHomCoatoms (subspaceInternalSigmaEquiv k ⟨X, D⟩).1) = X := by
  have hbottom : (subspaceInternalSigmaEquiv k ⟨X, D⟩).1.1 ∅ = X :=
    ((subspaceQuotientEmbeddingEquiv X).symm D.toBottomEmbedding).2
  exact (topEmbedding_bottom_coatom_meet _).symm.trans hbottom

/-- Forward summands are precisely A_i/X for the actual reconstructed atoms. -/
theorem subspaceInternalSigmaEquiv_reconstructed_atom {k : ℕ}
    (f : TopBooleanEmbedding (Fin k) (Submodule R V)) (i : Fin k) :
    ((subspaceInternalSigmaEquiv k).symm f).2.1 i =
      (reconstructedAtom (topHomCoatoms f.1) i).map (f.1.1 ∅).mkQ := by
  rw [reconstructedAtom_eq_meetFace_singleton, topHom_coatom_meetFace]
  rfl

/-- Inverse coatoms are the inverse images of sums of all other summands. -/
theorem subspaceInternalSigmaEquiv_coatom {k : ℕ} (X : Submodule R V)
    (D : OrderedInternalDecomposition R (V ⧸ X) k) (i : Fin k) :
    topHomCoatoms (subspaceInternalSigmaEquiv k ⟨X, D⟩).1 i =
      ((Finset.univ.erase i).sup D.1).comap X.mkQ := rfl

namespace OrderedInternalDecomposition

noncomputable def sumLinearEquiv {k : ℕ} (D : OrderedInternalDecomposition R V k) :
    (⨁ i : Fin k, D.1 i) ≃ₗ[R] V :=
  LinearEquiv.ofBijective (DirectSum.coeLinearMap D.1) D.2.1

@[simp] theorem sumLinearEquiv_of {k : ℕ} (D : OrderedInternalDecomposition R V k)
    (i : Fin k) (x : D.1 i) :
    D.sumLinearEquiv (DirectSum.of (fun i ↦ D.1 i) i x) = (x : V) :=
  DirectSum.coeLinearMap_of D.1 i x

end OrderedInternalDecomposition
end BooleanAntichainsKernel
