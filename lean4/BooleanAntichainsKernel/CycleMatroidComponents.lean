import BooleanAntichainsKernel.CycleMatroid

namespace BooleanAntichainsKernel

open scoped Classical

variable {α β : Type*}

/-- The original labelled forest and reachability-spanning condition.
The literal tree-in-each-component statement remains a separate consumer. -/
def ForestSpansComponents (G : Graph α β) (B : Set β) : Prop :=
  GraphEdgeForest G B ∧ ∀ x y : G.vertexSet,
    GraphReachable G B x y ↔ GraphReachable G G.edgeSet x y

theorem forestSpansComponents_component_count {G : Graph α β} {B : Set β}
    (hB : ForestSpansComponents G B) : graphComponentCount G B = graphConnectedComponentCount G := by
  change Nat.card (Quot (GraphReachable G B)) = Nat.card (Quot (GraphReachable G G.edgeSet))
  exact Nat.card_congr (Quot.congrRight hB.2)

variable (G : Graph α β) [Finite G.vertexSet] [Finite G.edgeSet]

theorem cycleMatroid_base_spans_components {B : Set β} (hB : (cycleMatroid G).IsBase B) :
    ForestSpansComponents G B := by
  have hforest := (cycleMatroid_indep_iff G B).mp hB.indep
  have hEdges : ∀ e ∈ G.edgeSet, ∀ x y : G.vertexSet,
      G.IsLink e x.1 y.1 → GraphReachable G B x y := by
    intro e he x y hlink
    by_contra hn
    have hins := graphEdgeForest_insert hforest ⟨e, he⟩ (x := x) (y := y) hlink hn
    have heq := hB.eq_of_subset_indep ((cycleMatroid_indep_iff G _).mpr hins) (Set.subset_insert e B)
    have heB : e ∈ B := heq.symm ▸ Set.mem_insert e B
    exact hn ⟨LabelledGraphWalk.cons ⟨e, he⟩ heB hlink (.nil y)⟩
  refine ⟨hforest, ?_⟩
  intro x y
  exact ⟨graphReachable_mono G hforest.1, graphReachable_le_of_edges hEdges x y⟩

theorem cycleMatroid_isBase_of_spans_components {B : Set β} (hB : ForestSpansComponents G B) :
    (cycleMatroid G).IsBase B := by
  apply ((cycleMatroid_indep_iff G B).mpr hB.1).isBase_of_maximal
  intro J hJ hBJ
  have hforestJ := (cycleMatroid_indep_iff G J).mp hJ
  apply Set.eq_of_subset_of_ncard_le hBJ ?_ hforestJ.finite
  have hc : graphComponentCount G B ≤ graphComponentCount G J :=
    graphComponentCount_antitone (fun x y h ↦
      (hB.2 x y).mpr (graphReachable_mono G hforestJ.1 h))
  have hbcount := graphForest_component_count hB.1
  have hjcount := graphForest_component_count hforestJ
  omega

theorem cycleMatroid_isBase_iff_spans_components (B : Set β) :
    (cycleMatroid G).IsBase B ↔ ForestSpansComponents G B :=
  ⟨cycleMatroid_base_spans_components G, cycleMatroid_isBase_of_spans_components G⟩

/-- A subtraction-free rank identity, derived through an actual base,
its literal forest cardinality and the original walk-component classes. -/
theorem cycleMatroid_rank_add_components :
    matroidRank (cycleMatroid G) (cycleMatroid G).E + graphConnectedComponentCount G =
      G.vertexSet.ncard := by
  obtain ⟨B, hB⟩ := (cycleMatroid G).exists_isBase
  have hspan := cycleMatroid_base_spans_components G hB
  have hr : matroidRank (cycleMatroid G) (cycleMatroid G).E = B.ncard := by
    change ((cycleMatroid G).eRk (cycleMatroid G).E).toNat = B.ncard
    rw [hB.isBasis_ground.eRk_eq_encard]
    rfl
  have hcount := graphForest_component_count hspan.1
  rw [forestSpansComponents_component_count hspan] at hcount
  rw [hr]
  exact hcount

theorem cycleMatroid_rank :
    matroidRank (cycleMatroid G) (cycleMatroid G).E =
      G.vertexSet.ncard - graphConnectedComponentCount G :=
  Nat.eq_sub_of_add_eq (cycleMatroid_rank_add_components G)

theorem cycleMatroid_base_card {B : Set β} (hB : (cycleMatroid G).IsBase B) :
    B.ncard = G.vertexSet.ncard - graphConnectedComponentCount G := by
  have hspan := cycleMatroid_base_spans_components G hB
  rw [graphForest_size_eq hspan.1, forestSpansComponents_component_count hspan]

end BooleanAntichainsKernel
