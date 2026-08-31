import BooleanAntichainsKernel.PartitionSubsetCarrier
import BooleanAntichainsKernel.FinitePartitionRelabel

namespace BooleanAntichainsKernel

open scoped Classical

variable {α : Type*} [DecidableEq α]
variable (s : Finset α)

theorem partitionFromToSubtype (P : Finpartition s) :
    partitionFromSubtype s (partitionToSubtype s P) = P := by
  apply Finpartition.ext
  rw [partitionFromSubtype_parts]
  ext C
  constructor
  · intro hC
    obtain ⟨B, hB, hBC⟩ := Finset.mem_map.mp hC
    obtain ⟨x, hx⟩ := (partitionToSubtype s P).nonempty_of_mem_parts hB
    have hpart : (partitionToSubtype s P).part x = B :=
      (partitionToSubtype s P).part_eq_of_mem hB hx
    have hc : P.part x.1 = C := (partitionToSubtype_part s P x).symm.trans
      ((congrArg (supportedBlockEmbedding s) hpart).trans hBC)
    exact hc ▸ (P.part_mem.mpr x.2)
  · intro hC
    obtain ⟨x, hx⟩ := P.nonempty_of_mem_parts hC
    let xx : s := ⟨x, P.le hC hx⟩
    have hc : supportedBlockEmbedding s ((partitionToSubtype s P).part xx) = C :=
      (partitionToSubtype_part s P xx).trans (P.part_eq_of_mem hC hx)
    exact Finset.mem_map.mpr ⟨(partitionToSubtype s P).part xx,
      (partitionToSubtype s P).part_mem.mpr (Finset.mem_univ xx), hc⟩

theorem partitionToFromSubtype (Q : Finpartition (Finset.univ : Finset s)) :
    partitionToSubtype s (partitionFromSubtype s Q) = Q := by
  apply finitePartition_ext_part
  intro x
  apply (supportedBlockEmbedding s).injective
  exact (partitionToSubtype_part s (partitionFromSubtype s Q) x).trans (partitionFromSubtype_part s Q x)

noncomputable def supportedPartitionEquiv :
    Finpartition s ≃ Finpartition (Finset.univ : Finset s) where
  toFun := partitionToSubtype s
  invFun := partitionFromSubtype s
  left_inv := partitionFromToSubtype s
  right_inv := partitionToFromSubtype s

theorem partitionFromSubtype_mono {Q R : Finpartition (Finset.univ : Finset s)} (h : Q ≤ R) :
    partitionFromSubtype s Q ≤ partitionFromSubtype s R := by
  intro C hC
  rw [partitionFromSubtype_parts] at hC
  obtain ⟨D, hD, rfl⟩ := Finset.mem_map.mp hC
  obtain ⟨E, hE, hDE⟩ := h hD
  refine ⟨supportedBlockEmbedding s E, ?_, ?_⟩
  · rw [partitionFromSubtype_parts]
    exact Finset.mem_map.mpr ⟨E, hE, rfl⟩
  · exact Finset.map_subset_map.mpr hDE

/-- Partitions of the literal finite subset and partitions of its
original member subtype are order-isomorphic, with all labels preserved. -/
noncomputable def supportedPartitionOrderIso :
    Finpartition s ≃o Finpartition (Finset.univ : Finset s) where
  toEquiv := supportedPartitionEquiv s
  map_rel_iff' := by
    intro P Q
    change partitionToSubtype s P ≤ partitionToSubtype s Q ↔ P ≤ Q
    constructor
    · intro h
      have hb := partitionFromSubtype_mono s h
      rw [partitionFromToSubtype, partitionFromToSubtype] at hb
      exact hb
    · intro h D hD
      have hDo : supportedBlockEmbedding s D ∈ P.parts := by
        rw [← partitionFromToSubtype s P, partitionFromSubtype_parts]
        exact Finset.mem_map.mpr ⟨D, hD, rfl⟩
      obtain ⟨C, hC, hDC⟩ := h hDo
      have hCn : C ∈ (partitionToSubtype s Q).parts.map (supportedBlockEmbedding s) := by
        rw [← partitionFromSubtype_parts, partitionFromToSubtype]
        exact hC
      obtain ⟨E, hE, hEC⟩ := Finset.mem_map.mp hCn
      refine ⟨E, hE, ?_⟩
      apply (Finset.map_subset_map (f := Function.Embedding.subtype _)).mp
      change supportedBlockEmbedding s D ⊆ supportedBlockEmbedding s E
      rw [hEC]
      exact hDC

theorem partitionToSubtype_card (P : Finpartition s) :
    (partitionToSubtype s P).parts.card = P.parts.card := by
  have h := congrArg (fun Q : Finpartition s ↦ Q.parts.card) (partitionFromToSubtype s P)
  rw [partitionFromSubtype_card] at h
  exact h

/-- Cardinality is transported to the standard finite label set only
after the exact subset/member and vertex-bijection maps are proved. -/
noncomputable def supportedPartitionEquivFin :
    Finpartition s ≃ Finpartition (Finset.univ : Finset (Fin s.card)) :=
  (supportedPartitionEquiv s).trans (finitePartitionRelabelEquiv s.equivFin)

theorem supportedPartition_count_fin :
    Fintype.card (Finpartition s) = Fintype.card (Finpartition (Finset.univ : Finset (Fin s.card))) :=
  Fintype.card_congr (supportedPartitionEquivFin s)

end BooleanAntichainsKernel
