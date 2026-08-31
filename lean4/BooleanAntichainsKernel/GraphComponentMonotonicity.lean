import BooleanAntichainsKernel.ForestComponentCount

namespace BooleanAntichainsKernel

open scoped Classical

variable {α β : Type*} {G : Graph α β} {F H : Set β}

/-- If each original edge is connected by a walk in H, every original
F-walk is connected in H. This uses concatenation of labelled walks. -/
theorem graphReachable_le_of_edges
    (hEdges : ∀ e ∈ F, ∀ x y : G.vertexSet, G.IsLink e x.1 y.1 → GraphReachable G H x y)
    (x y : G.vertexSet) (h : GraphReachable G F x y) : GraphReachable G H x y := by
  obtain ⟨p⟩ := h
  induction p with
  | nil x => exact ⟨LabelledGraphWalk.nil x⟩
  | @cons x y z e he h p ih =>
    obtain ⟨q⟩ := hEdges e.1 he x y h
    obtain ⟨r⟩ := ih
    exact ⟨q.append r⟩

def graphWalkComponentMap
    (h : ∀ x y, GraphReachable G F x y → GraphReachable G H x y) :
    GraphWalkComponent G F → GraphWalkComponent G H := Quot.map id h

theorem graphWalkComponentMap_mk
    (h : ∀ x y, GraphReachable G F x y → GraphReachable G H x y) (x : G.vertexSet) :
    graphWalkComponentMap h (graphWalkComponentMk G F x) = graphWalkComponentMk G H x := rfl

theorem graphWalkComponentMap_surjective
    (h : ∀ x y, GraphReachable G F x y → GraphReachable G H x y) :
    Function.Surjective (graphWalkComponentMap h) := by
  intro q
  exact Quot.induction_on q (fun x ↦ ⟨graphWalkComponentMk G F x, rfl⟩)

theorem graphComponentCount_antitone [Finite G.vertexSet]
    (h : ∀ x y, GraphReachable G F x y → GraphReachable G H x y) :
    graphComponentCount G H ≤ graphComponentCount G F :=
  Nat.card_le_card_of_surjective _ (graphWalkComponentMap_surjective h)

/-- A larger forest has an edge joining two components of the smaller
forest. Otherwise the actual component quotient map contradicts the
proved forest edge/component identities. -/
theorem graphForest_exists_connecting_edge [Finite G.vertexSet] {I J : Set β}
    (hI : GraphEdgeForest G I) (hJ : GraphEdgeForest G J) (hcard : I.ncard < J.ncard) :
    ∃ e ∈ J, ∃ x y : G.vertexSet, G.IsLink e x.1 y.1 ∧ ¬GraphReachable G I x y := by
  by_contra hnone
  have hEdges : ∀ e ∈ J, ∀ x y : G.vertexSet, G.IsLink e x.1 y.1 → GraphReachable G I x y := by
    intro e he x y hlink
    by_contra hn
    exact hnone ⟨e, he, x, y, hlink, hn⟩
  have hc : graphComponentCount G I ≤ graphComponentCount G J :=
    graphComponentCount_antitone (fun x y h ↦ graphReachable_le_of_edges hEdges x y h)
  have hci := graphForest_component_count hI
  have hcj := graphForest_component_count hJ
  omega

end BooleanAntichainsKernel
