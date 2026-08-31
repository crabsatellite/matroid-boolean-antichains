import BooleanAntichainsKernel.GraphComponentMonotonicity

namespace BooleanAntichainsKernel

open scoped Classical

variable {α β : Type*} {G : Graph α β} {I : Set β}

/-- Add one original edge between two previously unreachable vertices.
The literal labelled-cycle forest predicate is recovered through the
already proved support equivalence, with new loop/parallel cases checked. -/
theorem graphEdgeForest_insert (hI : GraphEdgeForest G I) (e : G.edgeSet)
    {x y : G.vertexSet} (hlink : G.IsLink e.1 x.1 y.1) (hn : ¬GraphReachable G I x y) :
    GraphEdgeForest G (insert e.1 I) := by
  have hxy : x ≠ y := by
    intro h
    subst y
    exact hn ⟨LabelledGraphWalk.nil x⟩
  have hfresh : ∀ f : G.edgeSet, f.1 ∈ I → graphEdgeEnds G f ≠ graphEdgeEnds G e := by
    intro f hf heq
    have hfl : G.IsLink f.1 x.1 y.1 :=
      (graphEdgeEnds_eq_iff f x y).mp (heq.trans (graphEdgeEnds_eq e hlink))
    exact hn ⟨LabelledGraphWalk.cons f hf hfl (.nil y)⟩
  apply graphEdgeForest_iff_support.mpr
  refine ⟨Set.insert_subset e.2 hI.1, ?_, ?_, ?_⟩
  · intro a ha z hloop
    rcases ha with rfl | ha
    · have hx := hloop.eq_of_inc hlink.inc_left
      have hy := hloop.eq_of_inc hlink.inc_right
      exact hxy (Subtype.ext (hx.symm.trans hy))
    · exact hI.no_loops ha z hloop
  · intro a ha b hb hab
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact Subtype.ext (ha.trans hb.symm)
    · have hae : a = e := Subtype.ext ha
      subst a
      exact (hfresh b hb hab.symm).elim
    · have hbe : b = e := Subtype.ext hb
      subst b
      exact (hfresh a ha hab).elim
    · exact hI.ends_injOn ha hb hab
  · rw [graphSupport_insert I e hlink]
    have hn' : ¬(graphSupport G I).Reachable x y :=
      fun h ↦ hn ((graphReachable_iff_support G I x y).mpr h)
    exact SimpleGraph.IsAcyclic.sup_edge_of_not_reachable hn' hI.support_isAcyclic

/-- The actual finite-forest augmentation axiom. The new edge is a
labelled edge of J outside I, not merely a simple endpoint pair. -/
theorem graphEdgeForest_augment [Finite G.vertexSet] {J : Set β}
    (hI : GraphEdgeForest G I) (hJ : GraphEdgeForest G J) (hcard : I.ncard < J.ncard) :
    ∃ e ∈ J, e ∉ I ∧ GraphEdgeForest G (insert e I) := by
  obtain ⟨e, heJ, x, y, hlink, hn⟩ := graphForest_exists_connecting_edge hI hJ hcard
  have heI : e ∉ I := by
    intro he
    exact hn ⟨LabelledGraphWalk.cons ⟨e, hlink.edge_mem⟩ he hlink (.nil y)⟩
  exact ⟨e, heJ, heI, graphEdgeForest_insert hI ⟨e, hlink.edge_mem⟩ (x := x) (y := y) hlink hn⟩

end BooleanAntichainsKernel
