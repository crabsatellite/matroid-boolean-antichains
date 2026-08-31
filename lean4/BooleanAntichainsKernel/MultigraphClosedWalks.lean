import BooleanAntichainsKernel.MultigraphSubgraphWalks
import BooleanAntichainsKernel.MultigraphComponentPoints

namespace BooleanAntichainsKernel

variable {α β : Type*}

/-- The native graph restricted to the original edge set F and induced
on the original vertex set X. No relabelling is performed. -/
def graphWithin (G : Graph α β) (F : Set β) (X : Set α) : Graph α β :=
  (G.restrict F).induce X

theorem graphWithin_vertexSet (G : Graph α β) (F : Set β) (X : Set α) :
    (graphWithin G F X).vertexSet = X := rfl

theorem graphWithin_isLink (G : Graph α β) (F : Set β) (X : Set α) (e : β) (x y : α) :
    (graphWithin G F X).IsLink e x y ↔ (e ∈ F ∧ G.IsLink e x y) ∧ x ∈ X ∧ y ∈ X := Iff.rfl

theorem graphWithin_edge_subset (G : Graph α β) (F : Set β) (X : Set α) :
    (graphWithin G F X).edgeSet ⊆ F := by
  intro e he
  obtain ⟨x, y, h⟩ := (graphWithin G F X).exists_isLink_of_mem_edgeSet he
  exact h.1.1

theorem graphWithin_le (G : Graph α β) (F : Set β) {X : Set α} (hX : X ⊆ G.vertexSet) :
    graphWithin G F X ≤ G :=
  (Graph.induce_le (G := G.restrict F) hX).trans Graph.restrict_le

variable {G : Graph α β} {F : Set β} {X : Set α}

/-- Descend a labelled walk into a vertex set closed under original
links. Each selected original edge is certified in the native induced graph. -/
def LabelledGraphWalk.descendWithin
    (hclosed : ∀ e x y, G.IsLink e x y → x ∈ X → y ∈ X) {x y : G.vertexSet} :
    (p : LabelledGraphWalk G F x y) → (hx : x.1 ∈ X) → (hy : y.1 ∈ X) →
      LabelledGraphWalk (graphWithin G F X) (graphWithin G F X).edgeSet ⟨x.1, hx⟩ ⟨y.1, hy⟩
  | .nil x, hx, _hy => .nil ⟨x.1, hx⟩
  | @LabelledGraphWalk.cons _ _ _ _ x y z e he h p, hx, hz =>
    let hy : y.1 ∈ X := hclosed e.1 x.1 y.1 h hx
    let hh : (graphWithin G F X).IsLink e.1 x.1 y.1 := ⟨⟨he, h⟩, hx, hy⟩
    .cons (x := ⟨x.1, hx⟩) (y := ⟨y.1, hy⟩) (z := ⟨z.1, hz⟩)
      ⟨e.1, hh.edge_mem⟩ hh.edge_mem hh (p.descendWithin hclosed hy hz)

theorem LabelledGraphWalk.descendWithin_edgeLabels
    (hclosed : ∀ e x y, G.IsLink e x y → x ∈ X → y ∈ X) {x y : G.vertexSet}
    (p : LabelledGraphWalk G F x y) (hx : x.1 ∈ X) (hy : y.1 ∈ X) :
    (p.descendWithin hclosed hx hy).edgeLabels = p.edgeLabels := by
  revert hx hy
  induction p with
  | nil => intro _ _; rfl
  | @cons x y z e he h p ih =>
    intro hx hz
    change e.1 :: (p.descendWithin hclosed (hclosed e.1 x.1 y.1 h hx) hz).edgeLabels = e.1 :: p.edgeLabels
    exact congrArg (List.cons e.1) (ih _ _)

theorem LabelledGraphWalk.descendWithin_vertexLabels
    (hclosed : ∀ e x y, G.IsLink e x y → x ∈ X → y ∈ X) {x y : G.vertexSet}
    (p : LabelledGraphWalk G F x y) (hx : x.1 ∈ X) (hy : y.1 ∈ X) :
    (p.descendWithin hclosed hx hy).vertexLabels = p.vertexLabels := by
  revert hx hy
  induction p with
  | nil => intro _ _; rfl
  | @cons x y z e he h p ih =>
    intro hx hz
    change x.1 :: (p.descendWithin hclosed (hclosed e.1 x.1 y.1 h hx) hz).vertexLabels = x.1 :: p.vertexLabels
    exact congrArg (List.cons x.1) (ih _ _)

theorem LabelledGraphWalk.descendWithin_isCycle
    (hclosed : ∀ e x y, G.IsLink e x y → x ∈ X → y ∈ X) {x : G.vertexSet}
    (p : LabelledGraphWalk G F x x) (hx : x.1 ∈ X) :
    (p.descendWithin hclosed hx hx).IsCycle ↔ p.IsCycle := by
  rw [(p.descendWithin hclosed hx hx).isCycle_iff_originalLabels, p.isCycle_iff_originalLabels,
    p.descendWithin_edgeLabels hclosed hx hx, p.descendWithin_vertexLabels hclosed hx hx]

theorem graphReachable_descendWithin
    (hclosed : ∀ e x y, G.IsLink e x y → x ∈ X → y ∈ X) {x y : G.vertexSet}
    (h : GraphReachable G F x y) (hx : x.1 ∈ X) (hy : y.1 ∈ X) :
    GraphReachable (graphWithin G F X) (graphWithin G F X).edgeSet ⟨x.1, hx⟩ ⟨y.1, hy⟩ := by
  obtain ⟨p⟩ := h
  exact ⟨p.descendWithin hclosed hx hy⟩

end BooleanAntichainsKernel
