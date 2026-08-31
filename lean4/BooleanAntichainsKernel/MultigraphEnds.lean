import Mathlib.Combinatorics.Graph.Basic

namespace BooleanAntichainsKernel

open scoped Classical

variable {α β : Type*}

theorem graphEdge_has_vertex_pair (G : Graph α β) (e : G.edgeSet) :
    ∃ uv : G.vertexSet × G.vertexSet, G.IsLink e.1 uv.1.1 uv.2.1 := by
  obtain ⟨u, v, h⟩ := G.exists_isLink_of_mem_edgeSet e.2
  exact ⟨(⟨u, h.left_mem⟩, ⟨v, h.right_mem⟩), h⟩

/-- Choose only an orientation of the actual edge's original endpoints.
The unordered endpoint value below is proved independent of this choice. -/
noncomputable def graphEdgeEndpoints (G : Graph α β) (e : G.edgeSet) :
    {uv : G.vertexSet × G.vertexSet // G.IsLink e.1 uv.1.1 uv.2.1} :=
  ⟨(graphEdge_has_vertex_pair G e).choose, (graphEdge_has_vertex_pair G e).choose_spec⟩

noncomputable def graphEdgeEnds (G : Graph α β) (e : G.edgeSet) : Sym2 G.vertexSet :=
  s((graphEdgeEndpoints G e).1.1, (graphEdgeEndpoints G e).1.2)

theorem graphEdgeEnds_eq {G : Graph α β} (e : G.edgeSet) {u v : G.vertexSet}
    (h : G.IsLink e.1 u.1 v.1) : graphEdgeEnds G e = s(u, v) := by
  apply Sym2.eq_iff.mpr
  rcases (graphEdgeEndpoints G e).2.eq_and_eq_or_eq_and_eq h with ⟨hu, hv⟩ | ⟨hu, hv⟩
  · exact Or.inl ⟨Subtype.ext hu, Subtype.ext hv⟩
  · exact Or.inr ⟨Subtype.ext hu, Subtype.ext hv⟩

/-- The endpoint map recognizes exactly the original labelled incidence,
on the actual vertex set; no extra ambient vertices are introduced. -/
theorem graphEdgeEnds_eq_iff {G : Graph α β} (e : G.edgeSet) (u v : G.vertexSet) :
    graphEdgeEnds G e = s(u, v) ↔ G.IsLink e.1 u.1 v.1 := by
  constructor
  · intro h
    rcases Sym2.eq_iff.mp h with ⟨hu, hv⟩ | ⟨hu, hv⟩
    · simpa only [hu, hv] using (graphEdgeEndpoints G e).2
    · simpa only [hu, hv] using (graphEdgeEndpoints G e).2.symm
  · exact graphEdgeEnds_eq e

/-- Precisely loop edges map to diagonal endpoint pairs. -/
theorem graphEdgeEnds_isDiag_iff (G : Graph α β) (e : G.edgeSet) :
    (graphEdgeEnds G e).IsDiag ↔ ∃ x : α, G.IsLoopAt e.1 x := by
  rw [graphEdgeEnds, Sym2.mk_isDiag_iff]
  constructor
  · intro h
    refine ⟨(graphEdgeEndpoints G e).1.2.1, ?_⟩
    change G.IsLink e.1 (graphEdgeEndpoints G e).1.2.1 (graphEdgeEndpoints G e).1.2.1
    simpa only [h] using (graphEdgeEndpoints G e).2
  · rintro ⟨x, hx⟩
    have hu := hx.eq_of_inc (graphEdgeEndpoints G e).2.inc_left
    have hv := hx.eq_of_inc (graphEdgeEndpoints G e).2.inc_right
    exact Subtype.ext (hu.symm.trans hv)

/-- Endpoint equality is the exact same-link relation on original edges.
For the simplification, diagonal (loop) classes are separately deleted. -/
theorem graphEdgeEnds_eq_iff_same_link (G : Graph α β) (e f : G.edgeSet) :
    graphEdgeEnds G e = graphEdgeEnds G f ↔
      ∃ x y : α, G.IsLink e.1 x y ∧ G.IsLink f.1 x y := by
  constructor
  · intro h
    let uv := (graphEdgeEndpoints G e).1
    have hf : G.IsLink f.1 uv.1.1 uv.2.1 :=
      (graphEdgeEnds_eq_iff f uv.1 uv.2).mp h.symm
    exact ⟨uv.1.1, uv.2.1, (graphEdgeEndpoints G e).2, hf⟩
  · rintro ⟨x, y, he, hf⟩
    let u : G.vertexSet := ⟨x, he.left_mem⟩
    let v : G.vertexSet := ⟨y, he.right_mem⟩
    exact (graphEdgeEnds_eq e (u := u) (v := v) he).trans
      (graphEdgeEnds_eq f (u := u) (v := v) hf).symm

end BooleanAntichainsKernel
