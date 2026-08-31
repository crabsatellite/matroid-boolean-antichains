import BooleanAntichainsKernel.BottomEmbeddingIntervals
import Mathlib.LinearAlgebra.Quotient.Basic

namespace BooleanAntichainsKernel

open Finset
open scoped Classical

variable {R V ι : Type*} [Ring R] [AddCommGroup V] [Module R V]
variable [Fintype ι] [DecidableEq ι]

noncomputable instance [Fintype V] : Fintype (Submodule R V) :=
  Fintype.ofInjective (fun S : Submodule R V ↦ (S : Set V)) SetLike.coe_injective

/-- The genuine quotient by X, via the submodule correspondence theorem. -/
def subspaceQuotientEmbeddingEquiv (X : Submodule R V) :
    TopBooleanEmbeddingAtBottom ι (Submodule R V) X ≃
      BottomTopBooleanEmbedding ι (Submodule R (V ⧸ X)) :=
  (topEmbeddingAtBottomEquivIci X).trans
    (bottomTopBooleanEmbeddingCodomainEquiv (X.comapMkQRelIso.symm))

/-- Every face is sent to its actual image under the quotient map. -/
@[simp] theorem subspaceQuotientEmbeddingEquiv_apply (X : Submodule R V)
    (f : TopBooleanEmbeddingAtBottom ι (Submodule R V) X) (S : Finset ι) :
    (subspaceQuotientEmbeddingEquiv X f).1.1.1 S = (f.1.1.1 S).map X.mkQ := rfl

/-- The inverse takes the actual inverse image under the same quotient map. -/
@[simp] theorem subspaceQuotientEmbeddingEquiv_symm_apply (X : Submodule R V)
    (g : BottomTopBooleanEmbedding ι (Submodule R (V ⧸ X))) (S : Finset ι) :
    ((subspaceQuotientEmbeddingEquiv X).symm g).1.1.1 S =
      (g.1.1.1 S).comap X.mkQ := rfl

def subspaceQuotientSigmaEquiv :
    (Σ X : Submodule R V, BottomTopBooleanEmbedding ι (Submodule R (V ⧸ X))) ≃
      TopBooleanEmbedding ι (Submodule R V) :=
  (Equiv.sigmaCongrRight fun X ↦ (subspaceQuotientEmbeddingEquiv (ι := ι) X).symm).trans
    topEmbeddingBottomSigmaEquiv

theorem quotient_fibre_commonMeet {k : ℕ} (X : Submodule R V)
    (f : TopBooleanEmbeddingAtBottom (Fin k) (Submodule R V) X) :
    Finset.univ.inf (topHomCoatoms f.1.1) = X :=
  (topEmbedding_bottom_coatom_meet f.1).symm.trans f.2

theorem quotient_coatom_image {k : ℕ} (X : Submodule R V)
    (f : TopBooleanEmbeddingAtBottom (Fin k) (Submodule R V) X) (i : Fin k) :
    topHomCoatoms (subspaceQuotientEmbeddingEquiv X f).1.1 i =
      (topHomCoatoms f.1.1 i).map X.mkQ := rfl

end BooleanAntichainsKernel
