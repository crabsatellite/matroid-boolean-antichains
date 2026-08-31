import BooleanAntichainsKernel.EmbeddingBlockExtraction
import BooleanAntichainsKernel.UniformBlockEmbedding
import BooleanAntichainsKernel.SingletonAntichains

namespace BooleanAntichainsKernel

open Finset
open scoped Classical

variable {α : Type*} [Fintype α] [DecidableEq α] {E : Set α} {r k : ℕ}

lemma embeddingBlockFace_subset_ground {M : Matroid α}
    (f : TopBooleanEmbedding (Fin k) (MatroidFlat M)) (S : Finset (Fin k)) :
    (uniformBlockFace (embeddingBlockBottom f) (embeddingBlocks f) S : Set α) ⊆ M.E := by
  intro e he
  rcases Finset.mem_union.mp he with heX | heP
  · exact embeddingBlockBottom_subset_ground f heX
  · rcases Finset.mem_biUnion.mp heP with ⟨i, _, hei⟩
    exact embeddingBlocks_subset_ground f i hei

theorem uniformEmbedding_blockFace_small
    (f : TopBooleanEmbedding (Fin k) (MatroidFlat (uniformOn E r)))
    (S : Finset (Fin k)) (hS : S ≠ univ) :
    (uniformBlockFace (embeddingBlockBottom f) (embeddingBlocks f) S).card < r := by
  have hne : (f.1.1 S).1 ≠ E := fun h ↦
    topBooleanEmbedding_face_ne_top f S hS (Subtype.ext h)
  by_contra hn
  have hlarge : r ≤ (uniformBlockFace (embeddingBlockBottom f) (embeddingBlocks f) S).card :=
    Nat.le_of_not_gt hn
  have hc := uniformOn_closure_of_rank_le E r
    (uniformBlockFace (embeddingBlockBottom f) (embeddingBlocks f) S : Set α)
    (embeddingBlockFace_subset_ground f S)
    (by simpa only [Set.ncard_coe_finset] using hlarge)
  exact hne ((embedding_face_eq_closure_blocks f S).trans hc)

/-- The forward proper-face identity in the manuscript: every such image
is exactly the ordinary union of the bottom and the recovered blocks. -/
theorem uniformEmbedding_proper_face
    (f : TopBooleanEmbedding (Fin k) (MatroidFlat (uniformOn E r)))
    (S : Finset (Fin k)) (hS : S ≠ univ) :
    (f.1.1 S).1 = (uniformBlockFace (embeddingBlockBottom f) (embeddingBlocks f) S : Set α) :=
  (embedding_face_eq_closure_blocks f S).trans
    (uniformOn_closure_of_card_lt E r _ (embeddingBlockFace_subset_ground f S)
      (by simpa only [Set.ncard_coe_finset] using uniformEmbedding_blockFace_small f S hS))

theorem uniformEmbedding_full_union_rank (hr : r ≤ E.ncard)
    (f : TopBooleanEmbedding (Fin k) (MatroidFlat (uniformOn E r))) :
    r ≤ (uniformBlockFace (embeddingBlockBottom f) (embeddingBlocks f) univ).card := by
  by_contra hn
  have hsmall : (uniformBlockFace (embeddingBlockBottom f) (embeddingBlocks f) univ).card < r :=
    Nat.lt_of_not_ge hn
  have hc := uniformOn_closure_of_card_lt E r
    (uniformBlockFace (embeddingBlockBottom f) (embeddingBlocks f) univ : Set α)
    (embeddingBlockFace_subset_ground f univ)
    (by simpa only [Set.ncard_coe_finset] using hsmall)
  have ht : (f.1.1 univ).1 = E := congrArg Subtype.val f.1.2.2.2
  have hset : E = (uniformBlockFace (embeddingBlockBottom f) (embeddingBlocks f) univ : Set α) :=
    ht.symm.trans ((embedding_face_eq_closure_blocks f univ).trans hc)
  have hcard := congrArg Set.ncard hset
  rw [Set.ncard_coe_finset] at hcard
  omega

lemma empty_ne_univ_of_two_le (hk : 2 ≤ k) : (∅ : Finset (Fin k)) ≠ univ := by
  intro h
  have hc := congrArg Finset.card h
  simp only [Finset.card_empty, Finset.card_univ, Fintype.card_fin] at hc
  omega

lemma singleton_ne_univ_of_two_le (hk : 2 ≤ k) (i : Fin k) : ({i} : Finset (Fin k)) ≠ univ := by
  intro h
  have hc := congrArg Finset.card h
  simp only [Finset.card_singleton, Finset.card_univ, Fintype.card_fin] at hc
  omega

/-- Recover the paper's literal bottom and atom-difference blocks. -/
noncomputable def uniformEmbeddingToBlocks (hr : r ≤ E.ncard) (hk : 2 ≤ k)
    (f : TopBooleanEmbedding (Fin k) (MatroidFlat (uniformOn E r))) : UniformBlockData E r k where
  bottom := embeddingBlockBottom f
  blocks := embeddingBlocks f
  bottom_subset := embeddingBlockBottom_subset_ground f
  blocks_subset := embeddingBlocks_subset_ground f
  bottom_disjoint := embeddingBlocks_disjoint_bottom f
  blocks_pairwise := embeddingBlocks_pairwise f
  blocks_nonempty := embeddingBlocks_nonempty f
  bottom_small := by
    simpa only [uniformBlockFace_empty] using
      uniformEmbedding_blockFace_small f ∅ (empty_ne_univ_of_two_le hk)
  full_rank := uniformEmbedding_full_union_rank hr f
  coatom_small i := uniformEmbedding_blockFace_small f (univ.erase i)
    (fun h ↦ Finset.notMem_erase i univ (h.symm ▸ Finset.mem_univ i))

end BooleanAntichainsKernel
