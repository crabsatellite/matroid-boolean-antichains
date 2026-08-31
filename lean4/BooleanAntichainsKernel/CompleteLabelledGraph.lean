import BooleanAntichainsKernel.MultigraphReachability

namespace BooleanAntichainsKernel

open scoped Classical

/-- The complete simple graph on the original vertex type. Each edge is
the original unordered pair of two distinct vertices. -/
@[reducible] def completeLabelledGraph (α : Type*) : Graph α (Sym2 α) where
  vertexSet := Set.univ
  edgeSet := (⊤ : SimpleGraph α).edgeSet
  IsLink q x y := q = s(x, y) ∧ x ≠ y
  isLink_symm := by
    intro q _hq
    exact ⟨fun x y h ↦ ⟨h.1.trans Sym2.eq_swap, h.2.symm⟩⟩
  eq_or_eq_of_isLink_of_isLink := by
    intro q x y z w h h'
    rcases Sym2.eq_iff.mp (h.1.symm.trans h'.1) with ⟨hxz, _hyw⟩ | ⟨hxw, _hyz⟩
    · exact Or.inl hxz
    · exact Or.inr hxw
  edge_mem_iff_exists_isLink := by
    intro q
    induction q using Sym2.inductionOn with
    | _ x y =>
      constructor
      · intro h
        exact ⟨x, y, rfl, h⟩
      · rintro ⟨z, w, hq, hzw⟩
        rw [hq]
        exact hzw
  left_mem_of_isLink := fun _ _ _ _ ↦ Set.mem_univ _

variable {α : Type*}

theorem completeLabelledGraph_vertexSet :
    (completeLabelledGraph α).vertexSet = Set.univ := rfl

theorem completeLabelledGraph_isLink (q : Sym2 α) (x y : α) :
    (completeLabelledGraph α).IsLink q x y ↔ q = s(x, y) ∧ x ≠ y := Iff.rfl

theorem completeLabelledGraph_edge_mem (x y : α) :
    s(x, y) ∈ (completeLabelledGraph α).edgeSet ↔ x ≠ y := Iff.rfl

theorem completeLabelledGraph_no_loops (q : Sym2 α) (x : α) :
    ¬(completeLabelledGraph α).IsLoopAt q x := fun h ↦ h.2 rfl

theorem completeLabelledGraph_unique_edge {q t : Sym2 α} {x y : α}
    (hq : (completeLabelledGraph α).IsLink q x y)
    (ht : (completeLabelledGraph α).IsLink t x y) : q = t :=
  hq.1.trans ht.1.symm

def completeGraphVertex (x : α) : (completeLabelledGraph α).vertexSet := ⟨x, Set.mem_univ x⟩

def completeGraphVertexEquiv (α : Type*) : α ≃ (completeLabelledGraph α).vertexSet where
  toFun := completeGraphVertex
  invFun := Subtype.val
  left_inv _ := rfl
  right_inv _ := Subtype.ext rfl

theorem completeGraphVertexEquiv_val (x : α) :
    (completeGraphVertexEquiv α x).1 = x := rfl

instance [Finite α] : Finite (completeLabelledGraph α).vertexSet :=
  Finite.of_injective (Subtype.val : (completeLabelledGraph α).vertexSet → α) Subtype.val_injective

instance [Finite α] : Finite (completeLabelledGraph α).edgeSet :=
  Finite.of_injective (Subtype.val : (completeLabelledGraph α).edgeSet → Sym2 α) Subtype.val_injective

theorem completeLabelledGraph_reachable (x y : (completeLabelledGraph α).vertexSet) :
    GraphReachable (completeLabelledGraph α) (completeLabelledGraph α).edgeSet x y := by
  by_cases hxy : x = y
  · subst y
    exact ⟨LabelledGraphWalk.nil (G := completeLabelledGraph α) x⟩
  · have hne : x.1 ≠ y.1 := fun h ↦ hxy (Subtype.ext h)
    let e : (completeLabelledGraph α).edgeSet := ⟨s(x.1, y.1), hne⟩
    exact ⟨LabelledGraphWalk.cons (G := completeLabelledGraph α) (x := x) (y := y) (z := y)
      e e.2 ⟨rfl, hne⟩ (.nil y)⟩

theorem completeLabelledGraph_vertex_ncard :
    (completeLabelledGraph α).vertexSet.ncard = Nat.card α := by
  rw [← Nat.card_coe_set_eq]
  exact Nat.card_congr (completeGraphVertexEquiv α).symm

end BooleanAntichainsKernel
