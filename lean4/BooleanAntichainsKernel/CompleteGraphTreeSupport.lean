import BooleanAntichainsKernel.CompleteLabelledGraph
import BooleanAntichainsKernel.MultigraphSpanningTrees

namespace BooleanAntichainsKernel

open scoped Classical

variable {α : Type*}

/-- The support of an original complete-graph edge set and the simple
graph on the same original vertex labels are isomorphic by subtype value. -/
noncomputable def completeGraphSupportIso (F : Set (Sym2 α)) :
    graphSupport (completeLabelledGraph α) F ≃g SimpleGraph.fromEdgeSet F where
  toEquiv := (completeGraphVertexEquiv α).symm
  map_rel_iff' := by
    intro x y
    change (SimpleGraph.fromEdgeSet F).Adj x.1 y.1 ↔
      (graphSupport (completeLabelledGraph α) F).Adj x y
    rw [SimpleGraph.fromEdgeSet_adj, graphSupport_adj]
    constructor
    · rintro ⟨he, hne⟩
      exact ⟨fun h ↦ hne (congrArg Subtype.val h), s(x.1, y.1), he, rfl, hne⟩
    · rintro ⟨_hne, e, he, hlink⟩
      exact ⟨hlink.1 ▸ he, hlink.2⟩

theorem completeGraphSupportIso_val (F : Set (Sym2 α)) (x : (completeLabelledGraph α).vertexSet) :
    completeGraphSupportIso F x = x.1 := rfl

/-- Removing only vertex membership proofs restores each original
unordered edge label exactly. -/
theorem completeGraph_edgeEnds_original (e : (completeLabelledGraph α).edgeSet) :
    Sym2.map (Subtype.val : (completeLabelledGraph α).vertexSet → α)
      (graphEdgeEnds (completeLabelledGraph α) e) = e.1 := by
  change s((graphEdgeEndpoints (completeLabelledGraph α) e).1.1.1,
    (graphEdgeEndpoints (completeLabelledGraph α) e).1.2.1) = e.1
  exact (graphEdgeEndpoints (completeLabelledGraph α) e).2.1.symm

theorem completeGraph_edgeEnds_injective : Function.Injective (graphEdgeEnds (completeLabelledGraph α)) := by
  intro e f h
  apply Subtype.ext
  exact (completeGraph_edgeEnds_original e).symm.trans
    ((congrArg (Sym2.map (Subtype.val : (completeLabelledGraph α).vertexSet → α)) h).trans
      (completeGraph_edgeEnds_original f))

theorem completeSpanningTree_support_iff (F : Set (Sym2 α))
    (hF : F ⊆ (completeLabelledGraph α).edgeSet) :
    GraphSpanningTree (completeLabelledGraph α) F ↔ (graphSupport (completeLabelledGraph α) F).IsTree := by
  constructor
  · intro h
    refine { connected := ?_, isAcyclic := (graphSpanningTree_isForest h).support_isAcyclic }
    exact {
      preconnected := by
        intro x y
        exact (graphReachable_iff_support (completeLabelledGraph α) F x y).mp
          (graphSpanningTree_reachable h x y)
      nonempty := h.2.2.1 }
  · intro h
    have hf : GraphEdgeForest (completeLabelledGraph α) F := graphEdgeForest_iff_support.mpr
      ⟨hF, fun e _he x ↦ completeLabelledGraph_no_loops e x,
        completeGraph_edgeEnds_injective.injOn, h.isAcyclic⟩
    have hc : GraphIsConnected (completeLabelledGraph α) :=
      ⟨h.connected.nonempty, completeLabelledGraph_reachable⟩
    apply graphSpanningForest_isTree_of_connected hc
    apply forestSpansComponents_spanningForest
    refine ⟨hf, fun x y ↦ ?_⟩
    exact ⟨fun _ ↦ completeLabelledGraph_reachable x y,
      fun _ ↦ (graphReachable_iff_support (completeLabelledGraph α) F x y).mpr (h.connected x y)⟩

/-- The manuscript's native spanning trees and Mathlib's actual
connected-acyclic simple graphs agree on precisely the same edge set. -/
theorem completeSpanningTree_iff (F : Set (Sym2 α)) :
    GraphSpanningTree (completeLabelledGraph α) F ↔
      F ⊆ (completeLabelledGraph α).edgeSet ∧ (SimpleGraph.fromEdgeSet F).IsTree := by
  constructor
  · intro h
    exact ⟨h.1, (completeGraphSupportIso F).isTree_iff.mp ((completeSpanningTree_support_iff F h.1).mp h)⟩
  · rintro ⟨hF, ht⟩
    exact (completeSpanningTree_support_iff F hF).mpr ((completeGraphSupportIso F).isTree_iff.mpr ht)

end BooleanAntichainsKernel
