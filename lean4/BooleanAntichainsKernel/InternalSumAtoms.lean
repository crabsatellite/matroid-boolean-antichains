import BooleanAntichainsKernel.InternalSumEmbedding
import BooleanAntichainsKernel.ActiveAtoms

namespace BooleanAntichainsKernel

open Finset
open scoped Classical

variable {R V : Type*} [Ring R] [AddCommGroup V] [Module R V] {k : ℕ}

def bottomEmbeddingAtoms (f : BottomTopBooleanEmbedding (Fin k) (Submodule R V))
    (i : Fin k) : Submodule R V := f.1.1.1 {i}

theorem bottomEmbedding_eq_sup_atoms
    (f : BottomTopBooleanEmbedding (Fin k) (Submodule R V)) (S : Finset (Fin k)) :
    f.1.1.1 S = S.sup (bottomEmbeddingAtoms f) := by
  induction S using Finset.induction_on with
  | empty => simpa only [Finset.sup_empty] using f.2
  | @insert i S _ ih =>
    simpa only [Finset.sup_insert, ih, bottomEmbeddingAtoms] using
      topBooleanHom_insert f.1.1 i S

theorem bottomEmbeddingAtoms_ne_bot
    (f : BottomTopBooleanEmbedding (Fin k) (Submodule R V)) (i : Fin k) :
    bottomEmbeddingAtoms f i ≠ ⊥ := by
  intro h
  have heq : f.1.1.1 {i} = f.1.1.1 ∅ := h.trans f.2.symm
  have hs := f.1.2 heq
  simp at hs

theorem bottomEmbeddingAtoms_iSupIndep
    (f : BottomTopBooleanEmbedding (Fin k) (Submodule R V)) :
    iSupIndep (bottomEmbeddingAtoms f) := by
  apply iSupIndep_iff_supIndep_univ.mpr
  apply Finset.supIndep_iff_disjoint_erase.mpr
  intro i _
  apply disjoint_iff.mpr
  rw [← bottomEmbedding_eq_sup_atoms f (Finset.univ.erase i)]
  change f.1.1.1 {i} ⊓ f.1.1.1 (Finset.univ.erase i) = ⊥
  rw [← f.1.1.2.2.1, Finset.singleton_inter_of_notMem (Finset.notMem_erase i Finset.univ), f.2]

theorem bottomEmbeddingAtoms_iSup_eq_top
    (f : BottomTopBooleanEmbedding (Fin k) (Submodule R V)) :
    (⨆ i, bottomEmbeddingAtoms f i) = ⊤ := by
  have hs : Finset.univ.sup (bottomEmbeddingAtoms f) = ⊤ :=
    (bottomEmbedding_eq_sup_atoms f Finset.univ).symm.trans f.1.1.2.2.2
  simpa [Finset.sup_eq_iSup] using hs

/-- The paper's atomic summands form the actual internal direct sum. -/
def bottomEmbeddingToInternal (f : BottomTopBooleanEmbedding (Fin k) (Submodule R V)) :
    OrderedInternalDecomposition R V k :=
  ⟨bottomEmbeddingAtoms f,
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
      (bottomEmbeddingAtoms_iSupIndep f) (bottomEmbeddingAtoms_iSup_eq_top f),
    bottomEmbeddingAtoms_ne_bot f⟩

theorem internal_embedding_atoms (D : OrderedInternalDecomposition R V k) :
    bottomEmbeddingToInternal D.toBottomEmbedding = D := by
  apply Subtype.ext
  funext i
  change ({i} : Finset (Fin k)).sup D.1 = D.1 i
  exact Finset.sup_singleton

theorem embedding_internal_embedding (f : BottomTopBooleanEmbedding (Fin k) (Submodule R V)) :
    (bottomEmbeddingToInternal f).toBottomEmbedding = f := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext S
  exact (bottomEmbedding_eq_sup_atoms f S).symm

def bottomEmbeddingEquivInternal :
    BottomTopBooleanEmbedding (Fin k) (Submodule R V) ≃ OrderedInternalDecomposition R V k where
  toFun := bottomEmbeddingToInternal
  invFun := OrderedInternalDecomposition.toBottomEmbedding
  left_inv := embedding_internal_embedding
  right_inv := internal_embedding_atoms

end BooleanAntichainsKernel
