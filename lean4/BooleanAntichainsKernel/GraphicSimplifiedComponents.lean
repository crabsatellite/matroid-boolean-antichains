import BooleanAntichainsKernel.GraphicSimplifiedGraph
import BooleanAntichainsKernel.CycleMatroidForests

namespace BooleanAntichainsKernel

open scoped Classical

variable {α β : Type*}

instance (G : Graph α β) [Finite G.vertexSet] : Finite (graphSimplifiedGraph G).vertexSet := by
  change Finite G.vertexSet
  infer_instance

instance (G : Graph α β) [Finite G.vertexSet] : Finite (graphSimplifiedGraph G).edgeSet :=
  Finite.of_injective (Subtype.val : (graphSimplifiedGraph G).edgeSet → Sym2 G.vertexSet)
    Subtype.val_injective

theorem graphSimplifiedGraph_support_ground (G : Graph α β) :
    graphSupport (graphSimplifiedGraph G) (graphSimplifiedGraph G).edgeSet =
      graphSimplification G := by
  rw [graphSimplifiedGraph_support G _ (Set.Subset.refl _)]
  ext x y
  rw [SimpleGraph.fromEdgeSet_adj]
  constructor
  · exact fun h ↦ h.1
  · exact fun h ↦ ⟨h, h.ne⟩

theorem graphSimplifiedGraph_reachable (G : Graph α β) (T : Set (Sym2 G.vertexSet))
    (hT : T ⊆ (graphSimplification G).edgeSet) (x y : G.vertexSet) :
    GraphReachable (graphSimplifiedGraph G) T x y ↔
      (SimpleGraph.fromEdgeSet T).Reachable x y := by
  rw [graphReachable_iff_support, graphSimplifiedGraph_support G T hT]

theorem graphSimplifiedGraph_reachable_ground (G : Graph α β) (x y : G.vertexSet) :
    GraphReachable (graphSimplifiedGraph G) (graphSimplifiedGraph G).edgeSet x y ↔
      (graphSimplification G).Reachable x y := by
  rw [graphReachable_iff_support, graphSimplifiedGraph_support_ground]

theorem graphSimplifiedGraph_reachable_original (G : Graph α β) (x y : G.vertexSet) :
    GraphReachable (graphSimplifiedGraph G) (graphSimplifiedGraph G).edgeSet x y ↔
      GraphReachable G G.edgeSet x y :=
  (graphSimplifiedGraph_reachable_ground G x y).trans (graphReachable_iff_support G G.edgeSet x y).symm

/-- Identity on the original vertex labels induces the exact component
bijection. Isolated original vertices are included. -/
noncomputable def graphSimplifiedComponentsEquiv (G : Graph α β) :
    GraphWalkComponent (graphSimplifiedGraph G) (graphSimplifiedGraph G).edgeSet ≃
      GraphWalkComponent G G.edgeSet :=
  Quot.congrRight (graphSimplifiedGraph_reachable_original G)

theorem graphSimplifiedComponentsEquiv_mk (G : Graph α β) (x : G.vertexSet) :
    graphSimplifiedComponentsEquiv G
      (graphWalkComponentMk (graphSimplifiedGraph G) (graphSimplifiedGraph G).edgeSet x) =
        graphWalkComponentMk G G.edgeSet x := rfl

theorem graphSimplifiedGraph_component_count (G : Graph α β) :
    graphConnectedComponentCount (graphSimplifiedGraph G) = graphConnectedComponentCount G :=
  Nat.card_congr (graphSimplifiedComponentsEquiv G)

/-- This is the existing one-tree-per-original-component definition,
proved equivalent to simple-support acyclicity and identical reachable pairs. -/
theorem graphSimplifiedGraph_spanningForest_iff (G : Graph α β) (T : Set (Sym2 G.vertexSet)) :
    GraphSpanningForest (graphSimplifiedGraph G) T ↔
      T ⊆ (graphSimplification G).edgeSet ∧
        (SimpleGraph.fromEdgeSet T).IsAcyclic ∧
        ∀ x y : G.vertexSet,
          (SimpleGraph.fromEdgeSet T).Reachable x y ↔ (graphSimplification G).Reachable x y := by
  rw [graphSpanningForest_iff_spans_components]
  change (GraphEdgeForest (graphSimplifiedGraph G) T ∧ _) ↔ _
  rw [graphSimplifiedGraph_forest_iff]
  constructor
  · rintro ⟨⟨hT, hA⟩, hR⟩
    refine ⟨hT, hA, fun x y ↦ ?_⟩
    exact (graphSimplifiedGraph_reachable G T hT x y).symm.trans
      ((hR x y).trans (graphSimplifiedGraph_reachable_ground G x y))
  · rintro ⟨hT, hA, hR⟩
    refine ⟨⟨hT, hA⟩, fun x y ↦ ?_⟩
    exact (graphSimplifiedGraph_reachable G T hT x y).trans
      ((hR x y).trans (graphSimplifiedGraph_reachable_ground G x y).symm)

theorem graphSimplifiedGraph_cycleMatroid_indep (G : Graph α β) [Finite G.vertexSet]
    (T : Set (Sym2 G.vertexSet)) :
    (cycleMatroid (graphSimplifiedGraph G)).Indep T ↔
      T ⊆ (graphSimplification G).edgeSet ∧ (SimpleGraph.fromEdgeSet T).IsAcyclic :=
  graphSimplifiedGraph_forest_iff G T

theorem graphSimplifiedGraph_cycleMatroid_base (G : Graph α β) [Finite G.vertexSet]
    (T : Set (Sym2 G.vertexSet)) :
    (cycleMatroid (graphSimplifiedGraph G)).IsBase T ↔
      T ⊆ (graphSimplification G).edgeSet ∧
        (SimpleGraph.fromEdgeSet T).IsAcyclic ∧
        ∀ x y : G.vertexSet,
          (SimpleGraph.fromEdgeSet T).Reachable x y ↔ (graphSimplification G).Reachable x y :=
  (cycleMatroid_isBase_iff_spanningForest (graphSimplifiedGraph G) T).trans
    (graphSimplifiedGraph_spanningForest_iff G T)

end BooleanAntichainsKernel
