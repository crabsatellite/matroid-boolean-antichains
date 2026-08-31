import BooleanAntichainsKernel.PartitionCompleteFlatIso
import BooleanAntichainsKernel.GraphicConnected
import BooleanAntichainsKernel.RankTightFibers

namespace BooleanAntichainsKernel

open scoped Classical

variable {α : Type*}

/-- Components of the actual block-edge graph and the actual quotient
classes are identified by the original vertex label. -/
def completeSetoidComponentQuotientEquiv (s : Setoid α) :
    GraphWalkComponent (completeLabelledGraph α) (completeSetoidEdges s) ≃ Quotient s where
  toFun := Quot.lift (fun x : (completeLabelledGraph α).vertexSet ↦ Quotient.mk s x.1)
    (fun x y h ↦ Quotient.sound ((completeSetoid_reachable_iff s x y).mp h))
  invFun := Quotient.lift
    (fun x ↦ graphWalkComponentMk (completeLabelledGraph α) (completeSetoidEdges s) (completeGraphVertex x))
    (fun x y h ↦ Quot.sound ((completeSetoid_reachable_iff s (completeGraphVertex x) (completeGraphVertex y)).mpr h))
  left_inv q := Quot.inductionOn q (fun _ ↦ rfl)
  right_inv q := Quotient.inductionOn q (fun _ ↦ rfl)

theorem completeSetoidComponentQuotientEquiv_mk (s : Setoid α) (x : α) :
    completeSetoidComponentQuotientEquiv s
      (graphWalkComponentMk (completeLabelledGraph α) (completeSetoidEdges s) (completeGraphVertex x)) =
        Quotient.mk s x := rfl

theorem completeLabelledGraph_simple : GraphIsSimple (completeLabelledGraph α) :=
  ⟨completeLabelledGraph_no_loops, fun h h' ↦ completeLabelledGraph_unique_edge h h'⟩

theorem completeLabelledGraph_connected [Nonempty α] : GraphIsConnected (completeLabelledGraph α) :=
  ⟨Nonempty.map completeGraphVertex inferInstance, completeLabelledGraph_reachable⟩

theorem completeLabelledGraph_matroid_rank [Finite α] [Nonempty α] :
    matroidRank (cycleMatroid (completeLabelledGraph α)) (cycleMatroid (completeLabelledGraph α)).E =
      Nat.card α - 1 := by
  rw [cycleMatroid_rank, completeLabelledGraph_vertex_ncard,
    graphIsConnected_component_count (completeLabelledGraph α) completeLabelledGraph_connected]

section Partitions

variable [Fintype α] [DecidableEq α]

noncomputable def partitionFlatComponentsEquivBlocks (P : Finpartition (Finset.univ : Finset α)) :
    GraphWalkComponent (completeLabelledGraph α) (finitePartitionCompleteFlatOrderIso P).1 ≃ P.parts :=
  (completeSetoidComponentQuotientEquiv (finitePartitionSetoid P)).trans (finitePartitionQuotientBlockEquiv P)

theorem partitionFlatComponentsEquivBlocks_mk (P : Finpartition (Finset.univ : Finset α)) (x : α) :
    (partitionFlatComponentsEquivBlocks P (graphWalkComponentMk (completeLabelledGraph α)
      (finitePartitionCompleteFlatOrderIso P).1 (completeGraphVertex x))).1 = P.part x := rfl

theorem partitionFlat_component_count (P : Finpartition (Finset.univ : Finset α)) :
    graphComponentCount (completeLabelledGraph α) (finitePartitionCompleteFlatOrderIso P).1 = P.parts.card := by
  calc
    _ = Nat.card P.parts := Nat.card_congr (partitionFlatComponentsEquivBlocks P)
    _ = _ := by simp only [Nat.card_eq_fintype_card, Fintype.card_coe]

/-- The flat rank plus its actual number of blocks is the original
vertex count. The subtractive form is derived only afterwards. -/
theorem partitionFlat_rank_add_blocks (P : Finpartition (Finset.univ : Finset α)) :
    MatroidFlat.rank (finitePartitionCompleteFlatOrderIso P) + P.parts.card = Fintype.card α := by
  have h := cycleMatroid_rank_set_add_components (completeLabelledGraph α)
    (finitePartitionCompleteFlatOrderIso P).1 (finitePartitionCompleteFlatOrderIso P).2.subset_ground
  rw [partitionFlat_component_count, completeLabelledGraph_vertex_ncard, Nat.card_eq_fintype_card] at h
  exact h

theorem partitionFlat_rank (P : Finpartition (Finset.univ : Finset α)) :
    MatroidFlat.rank (finitePartitionCompleteFlatOrderIso P) = Fintype.card α - P.parts.card :=
  Nat.eq_sub_of_add_eq (partitionFlat_rank_add_blocks P)

theorem partitionFlat_hasCorank_iff [Nonempty α] (k : ℕ) (P : Finpartition (Finset.univ : Finset α)) :
    HasCorank (cycleMatroid (completeLabelledGraph α)) k (finitePartitionCompleteFlatOrderIso P) ↔
      P.parts.card = k + 1 := by
  rw [hasCorank_iff_add]
  have hsum := partitionFlat_rank_add_blocks P
  have htop : MatroidFlat.rank (⊤ : MatroidFlat (cycleMatroid (completeLabelledGraph α))) =
      Fintype.card α - 1 := by
    change matroidRank (cycleMatroid (completeLabelledGraph α)) (cycleMatroid (completeLabelledGraph α)).E = _
    rw [completeLabelledGraph_matroid_rank, Nat.card_eq_fintype_card]
  have hn : 0 < Fintype.card α := Fintype.card_pos
  rw [htop]
  omega

end Partitions

end BooleanAntichainsKernel
