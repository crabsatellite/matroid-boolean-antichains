import BooleanAntichainsKernel.PartitionBlockRecurrence

namespace BooleanAntichainsKernel

open scoped Classical

variable {α β : Type*}

def partitionFinsetOrderIso (e : α ≃ β) : Finset α ≃o Finset β where
  toEquiv := e.finsetCongr
  map_rel_iff' := by
    intro S T
    exact Finset.map_subset_map (f := e.toEmbedding)

variable [Fintype α] [Fintype β]

theorem partitionFinsetOrderIso_univ (e : α ≃ β) :
    partitionFinsetOrderIso e Finset.univ = Finset.univ :=
  map_top (partitionFinsetOrderIso e)

variable [DecidableEq α] [DecidableEq β]

/-- Apply the specified bijection to every original vertex in every
block. The native map/copy constructors preserve the actual block family. -/
noncomputable def finitePartitionRelabel (e : α ≃ β) (P : Finpartition (Finset.univ : Finset α)) :
    Finpartition (Finset.univ : Finset β) :=
  (P.map (partitionFinsetOrderIso e)).copy (partitionFinsetOrderIso_univ e)

theorem finitePartitionRelabel_parts (e : α ≃ β) (P : Finpartition (Finset.univ : Finset α)) :
    (finitePartitionRelabel e P).parts = P.parts.map (partitionFinsetOrderIso e).toEquiv.toEmbedding := rfl

theorem finitePartitionRelabel_left_inverse (e : α ≃ β)
    (P : Finpartition (Finset.univ : Finset α)) :
    finitePartitionRelabel e.symm (finitePartitionRelabel e P) = P := by
  apply Finpartition.ext
  rw [finitePartitionRelabel_parts, finitePartitionRelabel_parts, Finset.map_map]
  have hcomp : (partitionFinsetOrderIso e).toEquiv.toEmbedding.trans
      (partitionFinsetOrderIso e.symm).toEquiv.toEmbedding = Function.Embedding.refl (Finset α) := by
    apply Function.Embedding.ext
    intro S
    change e.symm.finsetCongr (e.finsetCongr S) = S
    exact e.finsetCongr.symm_apply_apply S
  rw [hcomp, Finset.map_refl]

noncomputable def finitePartitionRelabelEquiv (e : α ≃ β) :
    Finpartition (Finset.univ : Finset α) ≃ Finpartition (Finset.univ : Finset β) where
  toFun := finitePartitionRelabel e
  invFun := finitePartitionRelabel e.symm
  left_inv := finitePartitionRelabel_left_inverse e
  right_inv P := finitePartitionRelabel_left_inverse e.symm P

theorem finitePartitionRelabel_card (e : α ≃ β) (P : Finpartition (Finset.univ : Finset α)) :
    (finitePartitionRelabel e P).parts.card = P.parts.card := by
  rw [finitePartitionRelabel_parts, Finset.card_map]

theorem finitePartitionRelabel_same_block (e : α ≃ β) (P : Finpartition (Finset.univ : Finset α))
    (x y : α) :
    (∃ B ∈ (finitePartitionRelabel e P).parts, e x ∈ B ∧ e y ∈ B) ↔
      ∃ B ∈ P.parts, x ∈ B ∧ y ∈ B := by
  rw [finitePartitionRelabel_parts]
  constructor
  · rintro ⟨B, hB, hx, hy⟩
    rcases Finset.mem_map.mp hB with ⟨C, hC, rfl⟩
    exact ⟨C, hC, (Finset.mem_map' e.toEmbedding).mp hx, (Finset.mem_map' e.toEmbedding).mp hy⟩
  · rintro ⟨B, hB, hx, hy⟩
    exact ⟨partitionFinsetOrderIso e B, Finset.mem_map.mpr ⟨B, hB, rfl⟩,
      Finset.mem_map_of_mem e.toEmbedding hx, Finset.mem_map_of_mem e.toEmbedding hy⟩

noncomputable def partitionsWithBlocksRelabelEquiv (e : α ≃ β) (k : ℕ) :
    PartitionsWithBlocks α k ≃ PartitionsWithBlocks β k :=
  Equiv.subtypeEquiv (finitePartitionRelabelEquiv e) (fun P ↦ by
    change P.parts.card = k ↔ (finitePartitionRelabel e P).parts.card = k
    rw [finitePartitionRelabel_card])

theorem partitionsWithBlocks_relabel_count (e : α ≃ β) (k : ℕ) :
    Fintype.card (PartitionsWithBlocks α k) = Fintype.card (PartitionsWithBlocks β k) :=
  Fintype.card_congr (partitionsWithBlocksRelabelEquiv e k)

end BooleanAntichainsKernel
