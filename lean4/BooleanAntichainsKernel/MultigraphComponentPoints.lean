import BooleanAntichainsKernel.MultigraphReachability

namespace BooleanAntichainsKernel

open scoped Classical

variable {α β : Type*}

/-- The original ambient vertex labels in an original walk-component. -/
def graphComponentPoints (G : Graph α β) (c : GraphWalkComponent G G.edgeSet) : Set α :=
  Subtype.val '' {x : G.vertexSet | graphWalkComponentMk G G.edgeSet x = c}

theorem graphComponentPoints_subset (G : Graph α β) (c : GraphWalkComponent G G.edgeSet) :
    graphComponentPoints G c ⊆ G.vertexSet := by
  rintro _ ⟨x, _hx, rfl⟩
  exact x.2

theorem mem_graphComponentPoints (G : Graph α β) (c : GraphWalkComponent G G.edgeSet)
    (x : G.vertexSet) : x.1 ∈ graphComponentPoints G c ↔ graphWalkComponentMk G G.edgeSet x = c := by
  constructor
  · rintro ⟨y, hy, hyx⟩
    have h : y = x := Subtype.ext hyx
    exact h ▸ hy
  · intro h
    exact ⟨x, h, rfl⟩

theorem graphComponentPoints_nonempty (G : Graph α β) (c : GraphWalkComponent G G.edgeSet) :
    (graphComponentPoints G c).Nonempty := by
  obtain ⟨x, hx⟩ := Quot.mk_surjective c
  exact ⟨x.1, (mem_graphComponentPoints G c x).mpr hx⟩

/-- A component contains both endpoints of every original edge incident
with one of its vertices, including loops and parallel edges. -/
theorem graphComponentPoints_closed (G : Graph α β) (c : GraphWalkComponent G G.edgeSet)
    {e : β} {x y : α} (hlink : G.IsLink e x y) (hx : x ∈ graphComponentPoints G c) :
    y ∈ graphComponentPoints G c := by
  let xx : G.vertexSet := ⟨x, hlink.left_mem⟩
  let yy : G.vertexSet := ⟨y, hlink.right_mem⟩
  have hxx := (mem_graphComponentPoints G c xx).mp hx
  have hreach : GraphReachable G G.edgeSet xx yy :=
    ⟨LabelledGraphWalk.cons ⟨e, hlink.edge_mem⟩ hlink.edge_mem hlink (.nil yy)⟩
  have heq : graphWalkComponentMk G G.edgeSet xx = graphWalkComponentMk G G.edgeSet yy :=
    Quot.sound hreach
  exact (mem_graphComponentPoints G c yy).mpr (heq.symm.trans hxx)

/-- Reachability inside the actual component is obtained using the
proved equivalence-relation laws, not assumed from a component label. -/
theorem graphComponentPoints_reachable (G : Graph α β) (c : GraphWalkComponent G G.edgeSet)
    (x y : G.vertexSet) (hx : x.1 ∈ graphComponentPoints G c) (hy : y.1 ∈ graphComponentPoints G c) :
    GraphReachable G G.edgeSet x y := by
  have hxx := (mem_graphComponentPoints G c x).mp hx
  have hyy := (mem_graphComponentPoints G c y).mp hy
  let s : Setoid G.vertexSet := ⟨GraphReachable G G.edgeSet, graphReachable_equivalence G G.edgeSet⟩
  exact @Quotient.exact _ s x y (hxx.trans hyy.symm)

theorem graphComponentPoints_eq_of_common_vertex (G : Graph α β)
    (c d : GraphWalkComponent G G.edgeSet) {x : α}
    (hc : x ∈ graphComponentPoints G c) (hd : x ∈ graphComponentPoints G d) : c = d := by
  let xx : G.vertexSet := ⟨x, graphComponentPoints_subset G c hc⟩
  exact ((mem_graphComponentPoints G c xx).mp hc).symm.trans ((mem_graphComponentPoints G d xx).mp hd)

end BooleanAntichainsKernel
