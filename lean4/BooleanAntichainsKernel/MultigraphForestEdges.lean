import BooleanAntichainsKernel.MultigraphForestSupport

namespace BooleanAntichainsKernel

open scoped Classical

variable {α β : Type*} {G : Graph α β} {F : Set β}

/-- Send an actual forest edge to its endpoint edge. Both membership
certificates are proved from the original no-labelled-cycle predicate. -/
noncomputable def forestSupportEdge (hF : GraphEdgeForest G F) (e : F) :
    (graphSupport G F).edgeSet := by
  let ee : G.edgeSet := ⟨e.1, hF.1 e.2⟩
  refine ⟨graphEdgeEnds G ee, ?_⟩
  rw [graphSupport_edgeSet]
  refine ⟨⟨ee, e.2, rfl⟩, ?_⟩
  intro hd
  obtain ⟨x, hx⟩ := (graphEdgeEnds_isDiag_iff G ee).mp hd
  exact hF.no_loops e.2 x hx

theorem forestSupportEdge_injective (hF : GraphEdgeForest G F) :
    Function.Injective (forestSupportEdge hF) := by
  intro e f h
  apply Subtype.ext
  have he : (⟨e.1, hF.1 e.2⟩ : G.edgeSet) = ⟨f.1, hF.1 f.2⟩ :=
    hF.ends_injOn e.2 f.2 (congrArg Subtype.val h)
  exact congrArg (fun q : G.edgeSet ↦ q.1) he

theorem forestSupportEdge_surjective (hF : GraphEdgeForest G F) :
    Function.Surjective (forestSupportEdge hF) := by
  intro q
  have hq : q.1 ∈ (graphEdgeEnds G '' {e : G.edgeSet | e.1 ∈ F}) \ Sym2.diagSet :=
    (Set.ext_iff.mp (graphSupport_edgeSet G F) q.1).mp q.2
  obtain ⟨e, he, heq⟩ := hq.1
  exact ⟨⟨e.1, he⟩, Subtype.ext heq⟩

/-- No forest edge identity is lost under simplification. This exact
bijection is consumed before comparing edge counts. -/
noncomputable def forestEdgesEquivSupport (hF : GraphEdgeForest G F) :
    F ≃ (graphSupport G F).edgeSet :=
  Equiv.ofBijective (forestSupportEdge hF)
    ⟨forestSupportEdge_injective hF, forestSupportEdge_surjective hF⟩

theorem forestEdgesEquivSupport_apply (hF : GraphEdgeForest G F) (e : F) :
    (forestEdgesEquivSupport hF e).1 = graphEdgeEnds G ⟨e.1, hF.1 e.2⟩ := rfl

theorem forest_edge_ncard (hF : GraphEdgeForest G F) :
    F.ncard = Nat.card (graphSupport G F).edgeSet :=
  Nat.card_congr (forestEdgesEquivSupport hF)

/-- Finiteness follows from the actual vertex set, not from an assumption
that the ambient edge type has no other or parallel labels. -/
theorem GraphEdgeForest.finite [Finite G.vertexSet] (hF : GraphEdgeForest G F) : F.Finite := by
  letI : Finite F := Finite.of_equiv (graphSupport G F).edgeSet (forestEdgesEquivSupport hF).symm
  exact Set.toFinite F

end BooleanAntichainsKernel
