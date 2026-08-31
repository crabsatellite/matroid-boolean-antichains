import BooleanAntichainsKernel.MultigraphEnds
import Mathlib.Combinatorics.SimpleGraph.Operations

namespace BooleanAntichainsKernel

open scoped Classical

variable {α β : Type*}

/-- The simple support of an actual edge subset, on all and only the
original vertices. Its edge fibres are retained by graphEdgeEnds. -/
noncomputable def graphSupport (G : Graph α β) (F : Set β) : SimpleGraph G.vertexSet :=
  SimpleGraph.fromEdgeSet (graphEdgeEnds G '' {e : G.edgeSet | e.1 ∈ F})

theorem graphSupport_adj (G : Graph α β) (F : Set β) (x y : G.vertexSet) :
    (graphSupport G F).Adj x y ↔ x ≠ y ∧ ∃ e : β, e ∈ F ∧ G.IsLink e x.1 y.1 := by
  rw [graphSupport, SimpleGraph.fromEdgeSet_adj]
  constructor
  · rintro ⟨⟨e, he, heq⟩, hxy⟩
    exact ⟨hxy, e.1, he, (graphEdgeEnds_eq_iff e x y).mp heq⟩
  · rintro ⟨hxy, e, he, h⟩
    exact ⟨⟨⟨e, h.edge_mem⟩, he, graphEdgeEnds_eq _ h⟩, hxy⟩

theorem graphSupport_edgeSet (G : Graph α β) (F : Set β) :
    (graphSupport G F).edgeSet =
      (graphEdgeEnds G '' {e : G.edgeSet | e.1 ∈ F}) \ Sym2.diagSet :=
  SimpleGraph.edgeSet_fromEdgeSet _

theorem graphSupport_mono (G : Graph α β) {F H : Set β} (hFH : F ⊆ H) :
    graphSupport G F ≤ graphSupport G H := by
  intro x y h
  obtain ⟨hxy, e, he, hl⟩ := (graphSupport_adj G F x y).mp h
  exact (graphSupport_adj G H x y).mpr ⟨hxy, e, hFH he, hl⟩

@[simp] theorem graphSupport_empty (G : Graph α β) : graphSupport G ∅ = ⊥ := by
  ext x y
  simp [graphSupport_adj]

theorem graphSupport_union (G : Graph α β) (F H : Set β) :
    graphSupport G (F ∪ H) = graphSupport G F ⊔ graphSupport G H := by
  ext x y
  rw [graphSupport_adj, SimpleGraph.sup_adj, graphSupport_adj, graphSupport_adj]
  constructor
  · rintro ⟨hxy, e, he | he, hl⟩
    · exact Or.inl ⟨hxy, e, he, hl⟩
    · exact Or.inr ⟨hxy, e, he, hl⟩
  · rintro (⟨hxy, e, he, hl⟩ | ⟨hxy, e, he, hl⟩)
    · exact ⟨hxy, e, Or.inl he, hl⟩
    · exact ⟨hxy, e, Or.inr he, hl⟩

/-- A singleton edge has precisely its original endpoints in the support;
for a loop the corresponding simple edge is empty. -/
theorem graphSupport_singleton {G : Graph α β} (e : G.edgeSet) {x y : G.vertexSet}
    (h : G.IsLink e.1 x.1 y.1) : graphSupport G {e.1} = SimpleGraph.edge x y := by
  have hs : {f : G.edgeSet | f.1 ∈ ({e.1} : Set β)} = {e} := by
    ext f
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, Subtype.ext_iff]
  rw [graphSupport, hs, Set.image_singleton, graphEdgeEnds_eq e h]
  rfl

theorem graphSupport_insert {G : Graph α β} (F : Set β) (e : G.edgeSet) {x y : G.vertexSet}
    (h : G.IsLink e.1 x.1 y.1) :
    graphSupport G (insert e.1 F) = graphSupport G F ⊔ SimpleGraph.edge x y := by
  rw [← Set.singleton_union, graphSupport_union, graphSupport_singleton e h, sup_comm]

/-- Delete loops and identify parallel endpoint classes, keeping isolated
vertices. This is the actual graph simplification in the paper. -/
noncomputable def graphSimplification (G : Graph α β) : SimpleGraph G.vertexSet :=
  graphSupport G G.edgeSet

theorem graphSimplification_adj (G : Graph α β) (x y : G.vertexSet) :
    (graphSimplification G).Adj x y ↔ x ≠ y ∧ G.Adj x.1 y.1 := by
  rw [graphSimplification, graphSupport_adj]
  constructor
  · rintro ⟨hxy, e, _he, h⟩
    exact ⟨hxy, e, h⟩
  · rintro ⟨hxy, e, h⟩
    exact ⟨hxy, e, h.edge_mem, h⟩

end BooleanAntichainsKernel
