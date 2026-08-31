import BooleanAntichainsKernel.GlobalEnumerator

/-! Top-preserving Boolean lattice homomorphisms from `thm:product`.
There is deliberately no ambient-bottom preservation requirement: the
image of the Boolean bottom is part of the actual homomorphism data. -/

namespace BooleanAntichainsKernel

open Finset
open scoped Classical

variable {ι L : Type*} [Fintype ι] [DecidableEq ι] [Lattice L] [OrderTop L]

def IsTopBooleanHom (f : Finset ι → L) : Prop :=
  (∀ S T, f (S ∪ T) = f S ⊔ f T) ∧
  (∀ S T, f (S ∩ T) = f S ⊓ f T) ∧ f Finset.univ = ⊤

abbrev TopBooleanHom (ι : Type*) [Fintype ι] [DecidableEq ι]
    (L : Type*) [Lattice L] [OrderTop L] :=
  {f : Finset ι → L // IsTopBooleanHom f}

abbrev TopBooleanEmbedding (ι : Type*) [Fintype ι] [DecidableEq ι]
    (L : Type*) [Lattice L] [OrderTop L] :=
  {f : TopBooleanHom ι L // Function.Injective f.1}

noncomputable instance [Fintype L] : Fintype (TopBooleanHom ι L) := Subtype.fintype _
noncomputable instance [Fintype L] : Fintype (TopBooleanEmbedding ι L) := Subtype.fintype _

lemma topBooleanHom_mono (f : TopBooleanHom ι L) : Monotone f.1 := by
  intro S T hST
  have h := f.2.1 S T
  rw [Finset.union_eq_right.mpr hST] at h
  exact le_sup_left.trans_eq h.symm

def topHomCoatoms {k : ℕ} (f : TopBooleanHom (Fin k) L) (i : Fin k) : L :=
  f.1 (Finset.univ.erase i)

lemma topHom_coatom_inf {k : ℕ} (f : TopBooleanHom (Fin k) L) (D : Finset (Fin k)) :
    D.inf (topHomCoatoms f) = f.1 (Finset.univ \ D) := by
  induction D using Finset.induction_on with
  | empty => simp only [Finset.inf_empty, Finset.sdiff_empty, f.2.2.2]
  | @insert i D hi ih =>
    rw [Finset.inf_insert, ih, topHomCoatoms, ← f.2.2.1]
    have hs : (Finset.univ.erase i) ∩ (Finset.univ \ D) = Finset.univ \ insert i D := by
      ext j
      simp
    exact congrArg f.1 hs

lemma topHom_coatom_meetFace {k : ℕ} (f : TopBooleanHom (Fin k) L) (S : Finset (Fin k)) :
    meetFace (topHomCoatoms f) S = f.1 S := by
  rw [meetFace, topHom_coatom_inf, Finset.sdiff_sdiff_eq_self (Finset.subset_univ S)]

lemma topBooleanEmbedding_coatoms_isBoolean {k : ℕ} (f : TopBooleanEmbedding (Fin k) L) :
    IsBooleanTuple (topHomCoatoms f.1) := by
  constructor
  · intro S T hST
    apply f.2
    simpa only [topHom_coatom_meetFace] using hST
  · intro S T
    simp only [topHom_coatom_meetFace, f.1.2.1]

variable [OrderBot L]

def orderedBooleanToTopEmbedding {k : ℕ} (H : OrderedBooleanTuple k L) :
    TopBooleanEmbedding (Fin k) L :=
  ⟨⟨meetFace H.1, H.2.2, meetFace_inter H.1, meetFace_univ H.1⟩, H.2.1⟩

def topEmbeddingToOrderedBoolean {k : ℕ} (f : TopBooleanEmbedding (Fin k) L) :
    OrderedBooleanTuple k L := ⟨topHomCoatoms f.1, topBooleanEmbedding_coatoms_isBoolean f⟩

/-- The labelled embeddings counted by `e_k(L)` are precisely the ordered
Boolean antichains, with the actual coatom/meet-face maps in both directions. -/
def orderedBooleanEquivTopEmbedding (k : ℕ) :
    OrderedBooleanTuple k L ≃ TopBooleanEmbedding (Fin k) L where
  toFun := orderedBooleanToTopEmbedding
  invFun := topEmbeddingToOrderedBoolean
  left_inv H := by
    apply Subtype.ext
    funext i
    exact meetFace_complement_singleton H.1 i
  right_inv f := by
    apply Subtype.ext
    apply Subtype.ext
    funext S
    exact topHom_coatom_meetFace f.1 S

theorem topBooleanEmbedding_count [Fintype L] [DecidableEq L] (k : ℕ) :
    Fintype.card (TopBooleanEmbedding (Fin k) L) =
      Fintype.card (BooleanAntichain k L) * k.factorial := by
  rw [← Fintype.card_congr (orderedBooleanEquivTopEmbedding (L := L) k), card_orderedBooleanTuple]

end BooleanAntichainsKernel
