import BooleanAntichainsKernel.TopEmbeddingTransport
import Mathlib.Order.LatticeIntervals

namespace BooleanAntichainsKernel

open Finset
open scoped Classical

variable {ι L : Type*} [Fintype ι] [DecidableEq ι] [Lattice L] [OrderTop L]

/-- Every image is above the actual image of the Boolean bottom. -/
def liftBottomEmbeddingToIci (X : L) (f : TopBooleanEmbeddingAtBottom ι L X) :
    BottomTopBooleanEmbedding ι (Set.Ici X) := by
  refine ⟨⟨⟨fun S ↦ ⟨f.1.1.1 S,
    f.2.symm.le.trans (topBooleanHom_mono f.1.1 (Finset.empty_subset S))⟩, ?_⟩, ?_⟩, ?_⟩
  · exact ⟨fun S T ↦ Subtype.ext (f.1.1.2.1 S T),
      fun S T ↦ Subtype.ext (f.1.1.2.2.1 S T),
      Subtype.ext f.1.1.2.2.2⟩
  · intro S T h
    exact f.1.2 (congrArg Subtype.val h)
  · exact Subtype.ext f.2

def forgetBottomIciEmbedding (X : L) (g : BottomTopBooleanEmbedding ι (Set.Ici X)) :
    TopBooleanEmbeddingAtBottom ι L X := by
  refine ⟨⟨⟨fun S ↦ (g.1.1.1 S).1, ?_⟩, ?_⟩, ?_⟩
  · exact ⟨fun S T ↦ congrArg Subtype.val (g.1.1.2.1 S T),
      fun S T ↦ congrArg Subtype.val (g.1.1.2.2.1 S T),
      congrArg Subtype.val g.1.1.2.2.2⟩
  · intro S T h
    exact g.1.2 (Subtype.ext h)
  · exact congrArg Subtype.val g.2

def topEmbeddingAtBottomEquivIci (X : L) :
    TopBooleanEmbeddingAtBottom ι L X ≃ BottomTopBooleanEmbedding ι (Set.Ici X) where
  toFun := liftBottomEmbeddingToIci X
  invFun := forgetBottomIciEmbedding X
  left_inv f := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv g := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    funext S
    apply Subtype.ext
    rfl

@[simp] theorem liftBottomEmbeddingToIci_apply (X : L)
    (f : TopBooleanEmbeddingAtBottom ι L X) (S : Finset ι) :
    ((liftBottomEmbeddingToIci X f).1.1.1 S).1 = f.1.1.1 S := rfl

/-- Partition by the literal image of the empty face. -/
def topEmbeddingBottomSigmaEquiv :
    (Σ X : L, TopBooleanEmbeddingAtBottom ι L X) ≃ TopBooleanEmbedding ι L :=
  Equiv.sigmaFiberEquiv (fun f : TopBooleanEmbedding ι L ↦ f.1.1 ∅)

lemma topEmbedding_bottom_coatom_meet {k : ℕ} (f : TopBooleanEmbedding (Fin k) L) :
    f.1.1 ∅ = Finset.univ.inf (topHomCoatoms f.1) := by
  simpa only [Finset.sdiff_self] using (topHom_coatom_inf f.1 Finset.univ).symm

end BooleanAntichainsKernel
