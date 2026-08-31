import BooleanAntichainsKernel.MultigraphClosedWalks
import BooleanAntichainsKernel.CycleMatroidComponents

namespace BooleanAntichainsKernel

variable {α β : Type*}

/-- A nonempty connected original multigraph with no labelled cycle. -/
def LabelledGraphTree (G : Graph α β) : Prop :=
  GraphEdgeForest G G.edgeSet ∧ Nonempty G.vertexSet ∧
    ∀ x y : G.vertexSet, GraphReachable G G.edgeSet x y

/-- The paper's literal spanning forests: original edges of G, with one
spanning tree on every original connected component's full vertex set. -/
def GraphSpanningForest (G : Graph α β) (F : Set β) : Prop :=
  F ⊆ G.edgeSet ∧ ∀ c : GraphWalkComponent G G.edgeSet,
    LabelledGraphTree ((G.restrict F).induce (graphComponentPoints G c))

variable {G : Graph α β} {F : Set β}

theorem forestSpansComponents_component_tree (hF : ForestSpansComponents G F)
    (c : GraphWalkComponent G G.edgeSet) :
    LabelledGraphTree ((G.restrict F).induce (graphComponentPoints G c)) := by
  let X := graphComponentPoints G c
  let H := graphWithin G F X
  have hsub : H ≤ G := graphWithin_le G F (graphComponentPoints_subset G c)
  have heF : H.edgeSet ⊆ F := graphWithin_edge_subset G F X
  change LabelledGraphTree H
  refine ⟨graphEdgeForest_of_subgraph hsub (hF.1.mono heF) (Set.Subset.refl _), ?_, ?_⟩
  · obtain ⟨a, ha⟩ := graphComponentPoints_nonempty G c
    exact ⟨⟨a, ha⟩⟩
  · intro x y
    let xx : G.vertexSet := ⟨x.1, hsub.vertexSet_mono x.2⟩
    let yy : G.vertexSet := ⟨y.1, hsub.vertexSet_mono y.2⟩
    have hg := graphComponentPoints_reachable G c xx yy x.2 y.2
    have hf := (hF.2 xx yy).mpr hg
    exact graphReachable_descendWithin
      (fun _ _ _ h hx ↦ graphComponentPoints_closed G c h hx) hf x.2 y.2

theorem forestSpansComponents_spanningForest (hF : ForestSpansComponents G F) :
    GraphSpanningForest G F := ⟨hF.1.1, forestSpansComponents_component_tree hF⟩

/-- Every labelled cycle lies within the original component of its
starting vertex, where the selected component tree forbids that cycle. -/
theorem graphSpanningForest_isForest (hF : GraphSpanningForest G F) : GraphEdgeForest G F := by
  refine ⟨hF.1, ?_⟩
  intro x p hp
  let c := graphWalkComponentMk G G.edgeSet x
  have hx : x.1 ∈ graphComponentPoints G c := (mem_graphComponentPoints G c x).mpr rfl
  have hclosed : ∀ e a b, G.IsLink e a b → a ∈ graphComponentPoints G c → b ∈ graphComponentPoints G c :=
    fun _ _ _ h ha ↦ graphComponentPoints_closed G c h ha
  exact (hF.2 c).1.2 ⟨x.1, hx⟩ (p.descendWithin hclosed hx hx)
    ((p.descendWithin_isCycle hclosed hx).mpr hp)

theorem graphSpanningForest_spans_components (hF : GraphSpanningForest G F) :
    ForestSpansComponents G F := by
  refine ⟨graphSpanningForest_isForest hF, ?_⟩
  intro x y
  refine ⟨graphReachable_mono G hF.1, ?_⟩
  intro hg
  let c := graphWalkComponentMk G G.edgeSet x
  have hx : x.1 ∈ graphComponentPoints G c := (mem_graphComponentPoints G c x).mpr rfl
  have heq : graphWalkComponentMk G G.edgeSet x = graphWalkComponentMk G G.edgeSet y := Quot.sound hg
  have hy : y.1 ∈ graphComponentPoints G c := (mem_graphComponentPoints G c y).mpr heq.symm
  let H := graphWithin G F (graphComponentPoints G c)
  have hsub : H ≤ G := graphWithin_le G F (graphComponentPoints_subset G c)
  have hwithin : GraphReachable H H.edgeSet ⟨x.1, hx⟩ ⟨y.1, hy⟩ := (hF.2 c).2.2 _ _
  have hglobal := graphReachable_map_subgraph hsub hwithin
  exact graphReachable_mono G (graphWithin_edge_subset G F (graphComponentPoints G c)) hglobal

/-- Both directions return to the same original edge set F. -/
theorem graphSpanningForest_iff_spans_components :
    GraphSpanningForest G F ↔ ForestSpansComponents G F :=
  ⟨graphSpanningForest_spans_components, forestSpansComponents_spanningForest⟩

/-- The actual cycle-matroid bases and the paper's componentwise spanning
forests agree on the identical original edge subsets. -/
theorem cycleMatroid_isBase_iff_spanningForest (G : Graph α β)
    [Finite G.vertexSet] [Finite G.edgeSet] (F : Set β) :
    (cycleMatroid G).IsBase F ↔ GraphSpanningForest G F := by
  rw [graphSpanningForest_iff_spans_components]
  exact cycleMatroid_isBase_iff_spans_components G F

end BooleanAntichainsKernel
