import BooleanAntichainsKernel.FinitePartitionSetoid

namespace BooleanAntichainsKernel

open scoped Classical

variable {α : Type*} [DecidableEq α]
variable (s : Finset α)

/-- Add only support-membership proofs to the original vertices. -/
def supportedPartitionSetoid (P : Finpartition s) : Setoid s :=
  Setoid.ker (fun x : s ↦ P.part x.1)

noncomputable def partitionToSubtype (P : Finpartition s) :
    Finpartition (Finset.univ : Finset s) :=
  Finpartition.ofSetoid (supportedPartitionSetoid s P)

def supportedBlockEmbedding : Finset s ↪ Finset α :=
  ⟨fun B ↦ B.map (Function.Embedding.subtype _), Finset.map_injective _⟩

/-- Restore original vertex labels in every block. -/
noncomputable def partitionFromSubtype (Q : Finpartition (Finset.univ : Finset s)) : Finpartition s :=
  Finpartition.ofExistsUnique (Q.parts.map (supportedBlockEmbedding s))
    (by
      intro C hC
      obtain ⟨B, _hB, rfl⟩ := Finset.mem_map.mp hC
      exact Finset.map_subtype_subset B)
    (by
      intro x hx
      let xx : s := ⟨x, hx⟩
      let B := Q.part xx
      have hB : B ∈ Q.parts := Q.part_mem.mpr (Finset.mem_univ xx)
      have hxB : xx ∈ B := Q.mem_part (Finset.mem_univ xx)
      refine ⟨supportedBlockEmbedding s B,
        ⟨Finset.mem_map.mpr ⟨B, hB, rfl⟩, Finset.mem_map.mpr ⟨xx, hxB, rfl⟩⟩, ?_⟩
      intro C hC
      obtain ⟨D, hD, hDC⟩ := Finset.mem_map.mp hC.1
      have hxmap : xx.1 ∈ D.map (Function.Embedding.subtype _) := by
        change x ∈ supportedBlockEmbedding s D
        rw [hDC]
        exact hC.2
      have hxD : xx ∈ D := (Finset.mem_map' (Function.Embedding.subtype _)).mp hxmap
      have hDB : D = B := Q.eq_of_mem_parts hD hB hxD hxB
      exact hDC.symm.trans (congrArg (supportedBlockEmbedding s) hDB))
    (by
      intro h
      obtain ⟨B, hB, hEmpty⟩ := Finset.mem_map.mp h
      obtain ⟨x, hx⟩ := Q.nonempty_of_mem_parts hB
      have hm : x.1 ∈ supportedBlockEmbedding s B := Finset.mem_map.mpr ⟨x, hx, rfl⟩
      rw [hEmpty] at hm
      exact Finset.notMem_empty _ hm)

theorem partitionFromSubtype_parts (Q : Finpartition (Finset.univ : Finset s)) :
    (partitionFromSubtype s Q).parts = Q.parts.map (supportedBlockEmbedding s) := rfl

theorem partitionFromSubtype_part (Q : Finpartition (Finset.univ : Finset s)) (x : s) :
    (partitionFromSubtype s Q).part x.1 = supportedBlockEmbedding s (Q.part x) := by
  apply (partitionFromSubtype s Q).part_eq_of_mem
  · rw [partitionFromSubtype_parts]
    exact Finset.mem_map.mpr ⟨Q.part x, Q.part_mem.mpr (Finset.mem_univ x), rfl⟩
  · exact Finset.mem_map.mpr ⟨x, Q.mem_part (Finset.mem_univ x), rfl⟩

theorem partitionFromSubtype_card (Q : Finpartition (Finset.univ : Finset s)) :
    (partitionFromSubtype s Q).parts.card = Q.parts.card := by
  rw [partitionFromSubtype_parts, Finset.card_map]

theorem partitionToSubtype_member (P : Finpartition s) (x y : s) :
    y ∈ (partitionToSubtype s P).part x ↔ y.1 ∈ P.part x.1 := by
  change y ∈ (Finpartition.ofSetoid (supportedPartitionSetoid s P)).part x ↔ _
  rw [Finpartition.mem_part_ofSetoid_iff_rel]
  change P.part x.1 = P.part y.1 ↔ _
  exact eq_comm.trans (P.mem_part_iff_part_eq_part y.2 x.2).symm

theorem partitionToSubtype_part (P : Finpartition s) (x : s) :
    supportedBlockEmbedding s ((partitionToSubtype s P).part x) = P.part x.1 := by
  ext a
  change a ∈ ((partitionToSubtype s P).part x).map (Function.Embedding.subtype _) ↔ _
  constructor
  · intro ha
    obtain ⟨y, hy, hya⟩ := Finset.mem_map.mp ha
    exact hya ▸ ((partitionToSubtype_member s P x y).mp hy)
  · intro ha
    let aa : s := ⟨a, P.part_subset x.1 ha⟩
    exact Finset.mem_map.mpr ⟨aa, (partitionToSubtype_member s P x aa).mpr ha, rfl⟩

end BooleanAntichainsKernel
