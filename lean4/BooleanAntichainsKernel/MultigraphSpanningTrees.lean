import BooleanAntichainsKernel.CycleMatroidForests

namespace BooleanAntichainsKernel

variable {α β : Type*} {G : Graph α β} {F : Set β}

/-- Restrict a labelled walk to precisely its selected original edge set.
The native restriction keeps the original vertex set. -/
def LabelledGraphWalk.restrictEdges {x y : G.vertexSet} :
    LabelledGraphWalk G F x y →
      LabelledGraphWalk (G.restrict F) (G.restrict F).edgeSet x y
  | .nil x => .nil (G := G.restrict F) (F := (G.restrict F).edgeSet) x
  | @LabelledGraphWalk.cons _ _ _ _ x y z e he h p =>
    .cons (G := G.restrict F) (F := (G.restrict F).edgeSet)
      (x := x) (y := y) (z := z) ⟨e.1, ⟨e.2, he⟩⟩ ⟨e.2, he⟩ ⟨he, h⟩ p.restrictEdges

theorem LabelledGraphWalk.restrictEdges_edgeLabels {x y : G.vertexSet}
    (p : LabelledGraphWalk G F x y) : p.restrictEdges.edgeLabels = p.edgeLabels := by
  induction p with
  | nil => rfl
  | @cons x y z e he h p ih =>
    change e.1 :: p.restrictEdges.edgeLabels = e.1 :: p.edgeLabels
    exact congrArg (List.cons e.1) ih

theorem LabelledGraphWalk.restrictEdges_vertexLabels {x y : G.vertexSet}
    (p : LabelledGraphWalk G F x y) : p.restrictEdges.vertexLabels = p.vertexLabels := by
  induction p with
  | nil => rfl
  | @cons x y z e he h p ih =>
    change x.1 :: p.restrictEdges.vertexLabels = x.1 :: p.vertexLabels
    exact congrArg (List.cons x.1) ih

theorem LabelledGraphWalk.restrictEdges_isCycle {x : G.vertexSet}
    (p : LabelledGraphWalk G F x x) : p.restrictEdges.IsCycle ↔ p.IsCycle := by
  rw [p.restrictEdges.isCycle_iff_originalLabels, p.isCycle_iff_originalLabels,
    p.restrictEdges_edgeLabels, p.restrictEdges_vertexLabels]

/-- Connectedness of the original graph includes nonemptiness. -/
def GraphIsConnected (G : Graph α β) : Prop :=
  Nonempty G.vertexSet ∧ ∀ x y : G.vertexSet, GraphReachable G G.edgeSet x y

/-- A literal native spanning tree: retain all original vertices and
restrict only the edge set, obtaining a nonempty connected acyclic graph. -/
def GraphSpanningTree (G : Graph α β) (F : Set β) : Prop :=
  F ⊆ G.edgeSet ∧ LabelledGraphTree (G.restrict F)

theorem graphSpanningTree_isForest (hF : GraphSpanningTree G F) : GraphEdgeForest G F := by
  refine ⟨hF.1, ?_⟩
  intro x p hp
  exact hF.2.1.2 x p.restrictEdges ((p.restrictEdges_isCycle).mpr hp)

theorem graphSpanningTree_reachable (hF : GraphSpanningTree G F) (x y : G.vertexSet) :
    GraphReachable G F x y := by
  have hR := graphReachable_map_subgraph (Graph.restrict_le (G := G) (E₀ := F)) (hF.2.2.2 x y)
  exact graphReachable_mono G Set.inter_subset_right hR

theorem graphSpanningTree_spanningForest (hF : GraphSpanningTree G F) : GraphSpanningForest G F := by
  apply forestSpansComponents_spanningForest
  refine ⟨graphSpanningTree_isForest hF, fun x y ↦ ?_⟩
  exact ⟨graphReachable_mono G hF.1, fun _ ↦ graphSpanningTree_reachable hF x y⟩

theorem graphSpanningForest_isTree_of_connected (hG : GraphIsConnected G)
    (hF : GraphSpanningForest G F) : GraphSpanningTree G F := by
  have hforest := graphSpanningForest_isForest hF
  have hspan := graphSpanningForest_spans_components hF
  refine ⟨hF.1, ?_, hG.1, ?_⟩
  · exact graphEdgeForest_of_subgraph (Graph.restrict_le (G := G) (E₀ := F))
      (hforest.mono Set.inter_subset_right) (Set.Subset.refl _)
  · intro x y
    obtain ⟨p⟩ := (hspan.2 x y).mpr (hG.2 x y)
    exact ⟨p.restrictEdges⟩

theorem graphSpanningForest_iff_spanningTree (hG : GraphIsConnected G) :
    GraphSpanningForest G F ↔ GraphSpanningTree G F :=
  ⟨graphSpanningForest_isTree_of_connected hG, graphSpanningTree_spanningForest⟩

abbrev GraphSpanningTrees (G : Graph α β) :=
  {F : Finset β // GraphSpanningTree G (F : Set β)}

noncomputable instance (G : Graph α β) [Finite G.edgeSet] : Fintype (GraphSpanningTrees G) :=
  Fintype.ofInjective
    (fun T : GraphSpanningTrees G ↦ (⟨T.1, graphSpanningTree_spanningForest T.2⟩ : GraphSpanningForests G))
    (fun _ _ h ↦ Subtype.ext (congrArg (fun F : GraphSpanningForests G ↦ F.1) h))

/-- Identity on original finite edge sets; only the proved certificates
are changed by the connected-graph specialization. -/
def graphSpanningForestsEquivTrees (G : Graph α β) (hG : GraphIsConnected G) :
    GraphSpanningForests G ≃ GraphSpanningTrees G :=
  Equiv.subtypeEquiv (Equiv.refl (Finset β)) (fun _ ↦ graphSpanningForest_iff_spanningTree hG)

theorem graphSpanningForestsEquivTrees_val (G : Graph α β) (hG : GraphIsConnected G)
    (F : GraphSpanningForests G) : (graphSpanningForestsEquivTrees G hG F).1 = F.1 := rfl

theorem graphSpanningForestsEquivTrees_symm_val (G : Graph α β) (hG : GraphIsConnected G)
    (T : GraphSpanningTrees G) : ((graphSpanningForestsEquivTrees G hG).symm T).1 = T.1 := rfl

end BooleanAntichainsKernel
