import BooleanAntichainsKernel.CompleteGraphTreeSupport

namespace BooleanAntichainsKernel

open scoped Classical

variable {α : Type*}

theorem complete_fromEdgeSet_edges (F : Set (Sym2 α)) (hF : F ⊆ (completeLabelledGraph α).edgeSet) :
    (SimpleGraph.fromEdgeSet F).edgeSet = F := by
  rw [SimpleGraph.edgeSet_fromEdgeSet]
  apply Set.Subset.antisymm Set.sdiff_subset
  intro q hq
  exact ⟨hq, (SimpleGraph.not_isDiag_of_mem_edgeSet (G := (⊤ : SimpleGraph α)) (e := q)) (hF hq)⟩

section Finite

variable [Fintype α]

noncomputable def completeTreeToSimple (F : GraphSpanningTrees (completeLabelledGraph α)) :
    {G : SimpleGraph α // G.IsTree} :=
  ⟨SimpleGraph.fromEdgeSet (F.1 : Set (Sym2 α)), ((completeSpanningTree_iff _).mp F.2).2⟩

theorem simpleGraph_edgeFinset_ground (G : SimpleGraph α) :
    (G.edgeFinset : Set (Sym2 α)) ⊆ (completeLabelledGraph α).edgeSet := by
  rw [SimpleGraph.coe_edgeFinset]
  exact SimpleGraph.edgeSet_mono (show G ≤ (⊤ : SimpleGraph α) from le_top)

noncomputable def simpleTreeToComplete (G : {G : SimpleGraph α // G.IsTree}) :
    GraphSpanningTrees (completeLabelledGraph α) :=
  ⟨G.1.edgeFinset, (completeSpanningTree_iff _).mpr ⟨simpleGraph_edgeFinset_ground G.1, by
    simpa only [SimpleGraph.coe_edgeFinset, SimpleGraph.fromEdgeSet_edgeSet] using G.2⟩⟩

theorem completeTree_simple_left (F : GraphSpanningTrees (completeLabelledGraph α)) :
    simpleTreeToComplete (completeTreeToSimple F) = F := by
  apply Subtype.ext
  apply Finset.coe_injective
  simp only [simpleTreeToComplete, completeTreeToSimple, SimpleGraph.coe_edgeFinset]
  exact complete_fromEdgeSet_edges _ F.2.1

theorem completeTree_simple_right (G : {G : SimpleGraph α // G.IsTree}) :
    completeTreeToSimple (simpleTreeToComplete G) = G := by
  apply Subtype.ext
  change SimpleGraph.fromEdgeSet (↑G.1.edgeFinset : Set (Sym2 α)) = G.1
  rw [SimpleGraph.coe_edgeFinset, SimpleGraph.fromEdgeSet_edgeSet]

/-- Both carriers use the same original vertices and unordered edge
labels. The forward map's edge set and the inverse finite edge set are exact. -/
noncomputable def completeTreeEquivSimpleTree :
    GraphSpanningTrees (completeLabelledGraph α) ≃ {G : SimpleGraph α // G.IsTree} where
  toFun := completeTreeToSimple
  invFun := simpleTreeToComplete
  left_inv := completeTree_simple_left
  right_inv := completeTree_simple_right

theorem completeTreeEquivSimpleTree_edges (F : GraphSpanningTrees (completeLabelledGraph α)) :
    (completeTreeEquivSimpleTree F).1.edgeSet = (F.1 : Set (Sym2 α)) :=
  complete_fromEdgeSet_edges _ F.2.1

theorem completeTreeEquivSimpleTree_symm_edges (G : {G : SimpleGraph α // G.IsTree}) :
    (completeTreeEquivSimpleTree.symm G).1 = G.1.edgeFinset := rfl

end Finite

variable {β : Type*}

def simpleGraphRelabelIso (e : α ≃ β) (G : SimpleGraph α) : G ≃g G.comap e.symm where
  toEquiv := e
  map_rel_iff' := by
    intro x y
    change G.Adj (e.symm (e x)) (e.symm (e y)) ↔ G.Adj x y
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]

def simpleTreeRelabelEquiv (e : α ≃ β) :
    {G : SimpleGraph α // G.IsTree} ≃ {G : SimpleGraph β // G.IsTree} where
  toFun G := ⟨G.1.comap e.symm, (simpleGraphRelabelIso e G.1).isTree_iff.mp G.2⟩
  invFun G := ⟨G.1.comap e, (simpleGraphRelabelIso e.symm G.1).isTree_iff.mp G.2⟩
  left_inv G := by
    apply Subtype.ext
    ext x y
    change G.1.Adj (e.symm (e x)) (e.symm (e y)) ↔ G.1.Adj x y
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  right_inv G := by
    apply Subtype.ext
    ext x y
    change G.1.Adj (e (e.symm x)) (e (e.symm y)) ↔ G.1.Adj x y
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]

theorem simpleTreeRelabelEquiv_adj (e : α ≃ β) (G : {G : SimpleGraph α // G.IsTree}) (x y : α) :
    (simpleTreeRelabelEquiv e G).1.Adj (e x) (e y) ↔ G.1.Adj x y :=
  (simpleGraphRelabelIso e G.1).map_rel_iff

end BooleanAntichainsKernel
