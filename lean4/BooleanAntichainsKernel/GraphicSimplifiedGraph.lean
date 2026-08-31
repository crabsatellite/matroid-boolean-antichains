import BooleanAntichainsKernel.MultigraphForestSupport

namespace BooleanAntichainsKernel

open scoped Classical

variable {α β : Type*}

/-- Native graph realization of the actual simplification. Original vertex
labels (including isolates) are unchanged; edges are the non-diagonal
unordered endpoint pairs already proved to be the simple support. -/
@[reducible] noncomputable def graphSimplifiedGraph (G : Graph α β) : Graph α (Sym2 G.vertexSet) where
  vertexSet := G.vertexSet
  edgeSet := (graphSimplification G).edgeSet
  IsLink q x y := ∃ u v : G.vertexSet,
    q = s(u, v) ∧ x = u.1 ∧ y = v.1 ∧ (graphSimplification G).Adj u v
  isLink_symm := by
    intro q _hq
    refine ⟨?_⟩
    rintro x y ⟨u, v, hq, hx, hy, huv⟩
    exact ⟨v, u, hq.trans (Sym2.eq_swap), hy, hx, huv.symm⟩
  eq_or_eq_of_isLink_of_isLink := by
    rintro q x y z w ⟨u, v, hq, hx, hy, _huv⟩ ⟨a, b, hq', hz, hw, _hab⟩
    rcases Sym2.eq_iff.mp (hq.symm.trans hq') with ⟨hua, _hvb⟩ | ⟨hub, _hva⟩
    · exact Or.inl (hx.trans ((congrArg Subtype.val hua).trans hz.symm))
    · exact Or.inr (hx.trans ((congrArg Subtype.val hub).trans hw.symm))
  edge_mem_iff_exists_isLink := by
    intro q
    induction q using Sym2.inductionOn with
    | _ u v =>
      constructor
      · intro hq
        exact ⟨u.1, v.1, u, v, rfl, rfl, rfl, hq⟩
      · rintro ⟨x, y, a, b, hab, _hx, _hy, ha⟩
        rw [hab]
        exact ha
  left_mem_of_isLink := by
    rintro q x y ⟨u, v, _hq, hx, _hy, _ha⟩
    exact hx ▸ u.2

theorem graphSimplifiedGraph_vertexSet (G : Graph α β) :
    (graphSimplifiedGraph G).vertexSet = G.vertexSet := rfl

theorem graphSimplifiedGraph_edgeSet (G : Graph α β) :
    (graphSimplifiedGraph G).edgeSet = (graphSimplification G).edgeSet := rfl

theorem graphSimplifiedGraph_isLink (G : Graph α β) (q : Sym2 G.vertexSet)
    (x y : G.vertexSet) :
    (graphSimplifiedGraph G).IsLink q x.1 y.1 ↔
      q = s(x, y) ∧ (graphSimplification G).Adj x y := by
  constructor
  · rintro ⟨u, v, hq, hx, hy, huv⟩
    have hu : x = u := Subtype.ext hx
    have hv : y = v := Subtype.ext hy
    subst u
    subst v
    exact ⟨hq, huv⟩
  · rintro ⟨hq, hxy⟩
    exact ⟨x, y, hq, rfl, rfl, hxy⟩

theorem graphSimplifiedGraph_no_loops (G : Graph α β) (q : Sym2 G.vertexSet) (x : α) :
    ¬(graphSimplifiedGraph G).IsLoopAt q x := by
  rintro ⟨u, v, _hq, hx, hy, huv⟩
  exact huv.ne (Subtype.ext (hx.symm.trans hy))

theorem graphSimplifiedGraph_unique_edge (G : Graph α β)
    {q t : Sym2 G.vertexSet} {x y : α}
    (hq : (graphSimplifiedGraph G).IsLink q x y)
    (ht : (graphSimplifiedGraph G).IsLink t x y) : q = t := by
  let xx : G.vertexSet := ⟨x, hq.left_mem⟩
  let yy : G.vertexSet := ⟨y, hq.right_mem⟩
  exact ((graphSimplifiedGraph_isLink G q xx yy).mp hq).1.trans
    ((graphSimplifiedGraph_isLink G t xx yy).mp ht).1.symm

theorem graphSimplifiedGraph_edgeEnds (G : Graph α β)
    (e : (graphSimplifiedGraph G).edgeSet) :
    graphEdgeEnds (graphSimplifiedGraph G) e = e.1 := by
  let uv := (graphEdgeEndpoints (graphSimplifiedGraph G) e).1
  have hl : (graphSimplifiedGraph G).IsLink e.1 uv.1.1 uv.2.1 :=
    (graphEdgeEndpoints (graphSimplifiedGraph G) e).2
  exact (graphEdgeEnds_eq e hl).trans
    ((graphSimplifiedGraph_isLink G e.1 uv.1 uv.2).mp hl).1.symm

theorem graphSimplifiedGraph_support (G : Graph α β) (T : Set (Sym2 G.vertexSet))
    (hT : T ⊆ (graphSimplification G).edgeSet) :
    graphSupport (graphSimplifiedGraph G) T = SimpleGraph.fromEdgeSet T := by
  ext x y
  rw [graphSupport_adj, SimpleGraph.fromEdgeSet_adj]
  constructor
  · rintro ⟨hxy, q, hq, hl⟩
    have heq := ((graphSimplifiedGraph_isLink G q x y).mp hl).1
    exact ⟨heq ▸ hq, hxy⟩
  · rintro ⟨hq, hxy⟩
    exact ⟨hxy, s(x, y), hq,
      (graphSimplifiedGraph_isLink G _ x y).mpr ⟨rfl, hT hq⟩⟩

/-- Literal labelled forests of the native simplified graph are exactly
acyclic subsets of the original simple-support edge set. -/
theorem graphSimplifiedGraph_forest_iff (G : Graph α β) (T : Set (Sym2 G.vertexSet)) :
    GraphEdgeForest (graphSimplifiedGraph G) T ↔
      T ⊆ (graphSimplification G).edgeSet ∧ (SimpleGraph.fromEdgeSet T).IsAcyclic := by
  rw [graphEdgeForest_iff_support]
  constructor
  · rintro ⟨hT, _hNL, _hInj, hA⟩
    exact ⟨hT, (graphSimplifiedGraph_support G T hT) ▸ hA⟩
  · rintro ⟨hT, hA⟩
    refine ⟨hT, fun q _hq x ↦ graphSimplifiedGraph_no_loops G q x, ?_, ?_⟩
    · intro e _he f _hf h
      exact Subtype.ext ((graphSimplifiedGraph_edgeEnds G e).symm.trans
        (h.trans (graphSimplifiedGraph_edgeEnds G f)))
    · exact (graphSimplifiedGraph_support G T hT).symm ▸ hA

end BooleanAntichainsKernel
