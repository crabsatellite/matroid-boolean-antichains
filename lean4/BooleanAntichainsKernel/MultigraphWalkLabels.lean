import BooleanAntichainsKernel.MultigraphWalks

namespace BooleanAntichainsKernel.LabelledGraphWalk

variable {α β : Type*} {G : Graph α β} {F : Set β} {x y z : G.vertexSet}

/-- Vertex labels in the original ambient vertex type, in walk order. -/
def vertexLabels (p : LabelledGraphWalk G F x y) : List α := p.support.map Subtype.val

@[simp] theorem vertexLabels_nil (x : G.vertexSet) :
    (nil x : LabelledGraphWalk G F x x).vertexLabels = [x.1] := rfl

@[simp] theorem vertexLabels_cons (e : G.edgeSet) (he : e.1 ∈ F) (h : G.IsLink e.1 x.1 y.1)
    (p : LabelledGraphWalk G F y z) : (cons e he h p).vertexLabels = x.1 :: p.vertexLabels := rfl

@[simp] theorem edgeLabels_nil (x : G.vertexSet) :
    (nil x : LabelledGraphWalk G F x x).edgeLabels = [] := rfl

@[simp] theorem edgeLabels_cons (e : G.edgeSet) (he : e.1 ∈ F) (h : G.IsLink e.1 x.1 y.1)
    (p : LabelledGraphWalk G F y z) : (cons e he h p).edgeLabels = e.1 :: p.edgeLabels := rfl

theorem vertexLabels_tail_nodup_iff (p : LabelledGraphWalk G F x y) :
    p.vertexLabels.tail.Nodup ↔ p.support.tail.Nodup := by
  rw [vertexLabels, ← List.map_tail]
  exact List.nodup_map_iff Subtype.val_injective

/-- Cyclehood is fully determined by the original label sequences;
proof-only vertex and edge subtype certificates do not change multiplicity. -/
theorem isCycle_iff_originalLabels (p : LabelledGraphWalk G F x x) :
    p.IsCycle ↔ p.edgeLabels.Nodup ∧ p.edgeLabels ≠ [] ∧ p.vertexLabels.tail.Nodup := by
  rw [p.edgeLabels_nodup_iff, p.vertexLabels_tail_nodup_iff]
  simp only [IsCycle, edgeLabels, ne_eq, List.map_eq_nil_iff]

end BooleanAntichainsKernel.LabelledGraphWalk
