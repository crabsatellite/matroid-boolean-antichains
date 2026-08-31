import BooleanAntichainsKernel.GraphicForestBijectionAtoms

namespace BooleanAntichainsKernel

open scoped Classical

variable {α β : Type*}

/-- Literal simplicity: no loop links and at most one original edge
label for any unordered pair of vertices. -/
structure GraphIsSimple (G : Graph α β) : Prop where
  no_loops : ∀ e x, ¬G.IsLoopAt e x
  unique_edge : ∀ {e f x y}, G.IsLink e x y → G.IsLink f x y → e = f

variable (G : Graph α β) [Finite G.vertexSet] [Finite G.edgeSet]

theorem GraphIsSimple.edge_nonloop (hG : GraphIsSimple G) (e : G.edgeSet) :
    (cycleMatroid G).IsNonloop e.1 := by
  apply (cycleMatroid_isNonloop_ends_iff G e).mpr
  intro hd
  obtain ⟨x, hx⟩ := (graphEdgeEnds_isDiag_iff G e).mp hd
  exact hG.no_loops e.1 x hx

omit [Finite G.vertexSet] [Finite G.edgeSet] in
theorem GraphIsSimple.ends_injective (hG : GraphIsSimple G) :
    Function.Injective (graphEdgeEnds G) := by
  intro e f h
  obtain ⟨x, y, he, hf⟩ := (graphEdgeEnds_eq_iff_same_link G e f).mp h
  exact Subtype.ext (hG.unique_edge he hf)

noncomputable def graphSimpleEdgeMap (hG : GraphIsSimple G) (e : G.edgeSet) :
    (graphSimplification G).edgeSet :=
  cycleNonloopToSimpleEdge G e (hG.edge_nonloop G e)

theorem graphSimpleEdgeMap_val (hG : GraphIsSimple G) (e : G.edgeSet) :
    (graphSimpleEdgeMap G hG e).1 = graphEdgeEnds G e := rfl

theorem graphSimpleEdgeMap_bijective (hG : GraphIsSimple G) :
    Function.Bijective (graphSimpleEdgeMap G hG) := by
  constructor
  · intro e f h
    exact hG.ends_injective G (congrArg (fun t : (graphSimplification G).edgeSet ↦ t.1) h)
  · intro t
    obtain ⟨e, _he, het⟩ := graphSimpleEdge_has_nonloop G t
    exact ⟨e, Subtype.ext het⟩

noncomputable def graphSimpleEdgesEquiv (hG : GraphIsSimple G) :
    G.edgeSet ≃ (graphSimplification G).edgeSet :=
  Equiv.ofBijective (graphSimpleEdgeMap G hG) (graphSimpleEdgeMap_bijective G hG)

theorem graphSimpleEdgesEquiv_val (hG : GraphIsSimple G) (e : G.edgeSet) :
    (graphSimpleEdgesEquiv G hG e).1 = graphEdgeEnds G e := rfl

omit [Finite G.vertexSet] [Finite G.edgeSet] in
/-- Restoring original labels and then taking support is exactly the
endpoint image, for every subset of the actual edge ground. -/
theorem graphSupport_ground_image (X : Set G.edgeSet) :
    graphSupport G ((Subtype.val : G.edgeSet → β) '' X) =
      SimpleGraph.fromEdgeSet (graphEdgeEnds G '' X) := by
  have hpre : {e : G.edgeSet | e.1 ∈ (Subtype.val : G.edgeSet → β) '' X} = X := by
    ext e
    constructor
    · rintro ⟨f, hf, hfe⟩
      exact (Subtype.ext hfe : f = e) ▸ hf
    · intro he
      exact ⟨e, he, rfl⟩
  exact congrArg (fun Z : Set G.edgeSet ↦ SimpleGraph.fromEdgeSet (graphEdgeEnds G '' Z)) hpre

theorem graphSimpleEdges_image_ground (hG : GraphIsSimple G) (X : Set G.edgeSet) :
    graphEdgeEnds G '' X ⊆ (graphSimplification G).edgeSet := by
  rintro q ⟨e, _he, rfl⟩
  exact (graphSimpleEdgesEquiv G hG e).2

theorem graphSimpleEdges_image (hG : GraphIsSimple G) (X : Set G.edgeSet) :
    (Subtype.val : (graphSimplification G).edgeSet → Sym2 G.vertexSet) ''
      (graphSimpleEdgesEquiv G hG '' X) = graphEdgeEnds G '' X := by
  rw [Set.image_image]
  rfl

end BooleanAntichainsKernel
