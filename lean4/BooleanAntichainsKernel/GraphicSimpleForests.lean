import BooleanAntichainsKernel.GraphicSimpleEdges

namespace BooleanAntichainsKernel

open scoped Classical

variable {α β : Type*} (G : Graph α β) [Finite G.vertexSet] [Finite G.edgeSet]

attribute [local instance] cycleMatroidGroundFintype
attribute [local instance 100] matroidGroundFlatFintype matroidGroundBasesFintype

local notation "M" => cycleMatroid G
local notation "S" => graphSimplifiedGraph G
local notation "Q" => cycleMatroid (graphSimplifiedGraph G)

/-- Simplicity makes the endpoint map an exact relabelling of spanning
forests; all original vertices and their reachable pairs stay unchanged. -/
theorem graphSimple_spanningForest_transport (hG : GraphIsSimple G) (X : Set G.edgeSet) :
    GraphSpanningForest G ((Subtype.val : G.edgeSet → β) '' X) ↔
      GraphSpanningForest S (graphEdgeEnds G '' X) := by
  have hX : (Subtype.val : G.edgeSet → β) '' X ⊆ G.edgeSet := by
    rintro e ⟨f, _hf, rfl⟩
    exact f.2
  have hs := graphSupport_ground_image G X
  have hR (x y : G.vertexSet) :
      GraphReachable G ((Subtype.val : G.edgeSet → β) '' X) x y ↔
        (SimpleGraph.fromEdgeSet (graphEdgeEnds G '' X)).Reachable x y := by
    rw [graphReachable_iff_support, hs]
  rw [graphSpanningForest_iff_spans_components, graphSimplifiedGraph_spanningForest_iff]
  constructor
  · rintro ⟨hF, hspan⟩
    refine ⟨graphSimpleEdges_image_ground G hG X, hs ▸ hF.support_isAcyclic, fun x y ↦ ?_⟩
    exact (hR x y).symm.trans ((hspan x y).trans (graphReachable_iff_support G G.edgeSet x y))
  · rintro ⟨_hE, hA, hspan⟩
    refine ⟨?_, fun x y ↦ ?_⟩
    · exact graphEdgeForest_iff_support.mpr ⟨hX, fun e _he x ↦ hG.no_loops e x,
        (hG.ends_injective G).injOn, hs.symm ▸ hA⟩
    · exact (hR x y).trans ((hspan x y).trans (graphReachable_iff_support G G.edgeSet x y).symm)

theorem graphSimple_ground_base_transport (hG : GraphIsSimple G) (X : Set G.edgeSet) :
    (Matroid.restrictSubtype M (Matroid.E M)).IsBase X ↔
      (Matroid.restrictSubtype Q (Matroid.E Q)).IsBase (graphSimpleEdgesEquiv G hG '' X) := by
  rw [Matroid.restrictSubtype_ground_isBase_iff, Matroid.restrictSubtype_ground_isBase_iff]
  rw [cycleMatroid_isBase_iff_spanningForest G, cycleMatroid_isBase_iff_spanningForest S]
  change GraphSpanningForest G ((Subtype.val : G.edgeSet → β) '' X) ↔
    GraphSpanningForest S ((Subtype.val : (graphSimplification G).edgeSet → Sym2 G.vertexSet) ''
      (graphSimpleEdgesEquiv G hG '' X))
  rw [graphSimpleEdges_image]
  exact graphSimple_spanningForest_transport G hG X

noncomputable def graphSimpleGroundBasesEquiv (hG : GraphIsSimple G) :
    MatroidBases (Matroid.restrictSubtype M (Matroid.E M)) ≃
      MatroidBases (Matroid.restrictSubtype Q (Matroid.E Q)) :=
  Equiv.subtypeEquiv (graphSimpleEdgesEquiv G hG).finsetCongr (fun B ↦ by
    let B0 : Finset G.edgeSet := B
    have hb := graphSimple_ground_base_transport G hG (B0 : Set G.edgeSet)
    have heq : (↑((graphSimpleEdgesEquiv G hG).finsetCongr B0) : Set (graphSimplification G).edgeSet) =
        graphSimpleEdgesEquiv G hG '' (B0 : Set G.edgeSet) :=
      Finset.coe_map (graphSimpleEdgesEquiv G hG).toEmbedding B0
    exact hb.trans (Iff.of_eq (congrArg
      (Matroid.IsBase (Matroid.restrictSubtype Q (Matroid.E Q))) heq.symm)))

noncomputable def graphSimpleSpanningForestsEquiv (hG : GraphIsSimple G) :
    GraphSpanningForests G ≃ GraphSpanningForests S :=
  (cycleMatroidBasesEquivSpanningForests G).symm.trans
    ((matroidGroundBasesEquiv M).symm.trans
      ((graphSimpleGroundBasesEquiv G hG).trans
        ((matroidGroundBasesEquiv Q).trans (cycleMatroidBasesEquivSpanningForests S))))

theorem graphSimpleSpanningForestsEquiv_val (hG : GraphIsSimple G) (F : GraphSpanningForests G) :
    (graphSimpleSpanningForestsEquiv G hG F).1 =
      (F.1.subtype (fun e ↦ e ∈ G.edgeSet)).map ⟨graphEdgeEnds G, hG.ends_injective G⟩ := by
  change ((F.1.subtype (fun e ↦ e ∈ G.edgeSet)).map
    (graphSimpleEdgesEquiv G hG).toEmbedding).map (Function.Embedding.subtype _) = _
  rw [Finset.map_map]
  rfl

/-- The simple-graph clause, on the original edge-labelled forests. -/
noncomputable def graphicSimpleMaximumAntichainEquivForests (hG : GraphIsSimple G) :
    BooleanAntichain (MatroidFlat.rank (⊤ : MatroidFlat M)) (MatroidFlat M) ≃
      GraphSpanningForests G :=
  (graphicMaximumAntichainEquivForests G).trans (graphSimpleSpanningForestsEquiv G hG).symm

theorem graphicSimpleMaximumAntichain_count (hG : GraphIsSimple G) :
    Fintype.card (BooleanAntichain (MatroidFlat.rank (⊤ : MatroidFlat M)) (MatroidFlat M)) =
      Fintype.card (GraphSpanningForests G) :=
  Fintype.card_congr (graphicSimpleMaximumAntichainEquivForests G hG)

end BooleanAntichainsKernel
