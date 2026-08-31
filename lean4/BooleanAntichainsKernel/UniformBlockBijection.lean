import BooleanAntichainsKernel.UniformEmbeddingBlocks

namespace BooleanAntichainsKernel

open Finset
open scoped Classical

variable {α : Type*} [Fintype α] [DecidableEq α] {E : Set α} {r k : ℕ}

theorem embeddingBlockBottom_toEmbedding (hk : 2 ≤ k) (D : UniformBlockData E r k) :
    embeddingBlockBottom D.toEmbedding = D.bottom := by
  ext e
  change e ∈ (D.toFlat ∅).1.toFinset ↔ e ∈ D.bottom
  rw [Set.mem_toFinset, D.toFlat_val_of_proper ∅ (empty_ne_univ_of_two_le hk),
    uniformBlockFace_empty, Finset.mem_coe]

theorem embeddingBlocks_toEmbedding (hk : 2 ≤ k) (D : UniformBlockData E r k) :
    embeddingBlocks D.toEmbedding = D.blocks := by
  funext i
  ext e
  change e ∈ ((D.toFlat {i}).1 \ (D.toFlat ∅).1).toFinset ↔ e ∈ D.blocks i
  rw [Set.mem_toFinset, Set.mem_sdiff,
    D.toFlat_val_of_proper {i} (singleton_ne_univ_of_two_le hk i),
    D.toFlat_val_of_proper ∅ (empty_ne_univ_of_two_le hk)]
  simp only [uniformBlockFace, Finset.singleton_biUnion, Finset.biUnion_empty,
    Finset.union_empty, Finset.mem_coe, Finset.mem_union]
  constructor
  · intro h
    exact h.1.resolve_left h.2
  · intro he
    exact ⟨Or.inr he, fun heX ↦ (Finset.disjoint_left.mp (D.bottom_disjoint i)) heX he⟩

theorem uniformBlocks_embedding_blocks (hr : r ≤ E.ncard) (hk : 2 ≤ k)
    (D : UniformBlockData E r k) : uniformEmbeddingToBlocks hr hk D.toEmbedding = D := by
  apply uniformBlockData_ext
  · exact embeddingBlockBottom_toEmbedding hk D
  · exact embeddingBlocks_toEmbedding hk D

theorem uniformEmbedding_blocks_embedding (hr : r ≤ E.ncard) (hk : 2 ≤ k)
    (f : TopBooleanEmbedding (Fin k) (MatroidFlat (uniformOn E r))) :
    (uniformEmbeddingToBlocks hr hk f).toEmbedding = f := by
  apply Subtype.ext
  apply Subtype.ext
  funext S
  apply Subtype.ext
  exact (embedding_face_eq_closure_blocks f S).symm

/-- The full actual bottom/block classification for k at least two.
Both inverse laws consume the literal atom-difference reconstruction. -/
noncomputable def uniformBlocksEquivTopEmbedding (hr : r ≤ E.ncard) (hk : 2 ≤ k) :
    UniformBlockData E r k ≃ TopBooleanEmbedding (Fin k) (MatroidFlat (uniformOn E r)) where
  toFun := UniformBlockData.toEmbedding
  invFun := uniformEmbeddingToBlocks hr hk
  left_inv := uniformBlocks_embedding_blocks hr hk
  right_inv := uniformEmbedding_blocks_embedding hr hk

/-- The factorial is inherited from the proved labelled-embedding fibres,
not built into the definition of the block count. -/
theorem uniformBlockData_count (hr : r ≤ E.ncard) (hk : 2 ≤ k) :
    Fintype.card (UniformBlockData E r k) =
      Fintype.card (BooleanAntichain k (MatroidFlat (uniformOn E r))) * k.factorial := by
  rw [Fintype.card_congr (uniformBlocksEquivTopEmbedding hr hk), topBooleanEmbedding_count]

theorem uniformAntichain_count_blocks (hr : r ≤ E.ncard) (hk : 2 ≤ k) :
    Fintype.card (BooleanAntichain k (MatroidFlat (uniformOn E r))) =
      Fintype.card (UniformBlockData E r k) / k.factorial := by
  rw [uniformBlockData_count hr hk, Nat.mul_div_cancel _ (Nat.factorial_pos k)]

end BooleanAntichainsKernel
