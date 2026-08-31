import BooleanAntichainsKernel.CycleMatroidRankOne

namespace BooleanAntichainsKernel

open scoped Classical

variable {α β : Type*} (G : Graph α β) [Finite G.vertexSet] [Finite G.edgeSet]

theorem graphSimpleEdge_has_nonloop (t : (graphSimplification G).edgeSet) :
    ∃ e : G.edgeSet, (cycleMatroid G).IsNonloop e.1 ∧ graphEdgeEnds G e = t.1 := by
  have ht : t.1 ∈ (graphEdgeEnds G '' {e : G.edgeSet | e.1 ∈ G.edgeSet}) \ Sym2.diagSet :=
    (Set.ext_iff.mp (graphSupport_edgeSet G G.edgeSet) t.1).mp t.2
  obtain ⟨e, _he, heq⟩ := ht.1
  have hN : (cycleMatroid G).IsNonloop e.1 := (cycleMatroid_isNonloop_ends_iff G e).mpr (by
    intro hd
    have hdt : t.1.IsDiag := heq ▸ hd
    exact ht.2 hdt)
  exact ⟨e, hN, heq⟩

theorem cycleRankOneToSimpleEdge_injective : Function.Injective (cycleRankOneToSimpleEdge G) := by
  intro A B h
  have hEnds : graphEdgeEnds G (cycleRankOneEdge G A) = graphEdgeEnds G (cycleRankOneEdge G B) :=
    congrArg (fun t : (graphSimplification G).edgeSet ↦ t.1) h
  have hcl := (cycleMatroid_singleton_closure_eq_iff G (cycleRankOneEdge G A) (cycleRankOneEdge G B)
    (cycleRankOneEdge_spec G A).1 (cycleRankOneEdge_spec G B).1).mpr hEnds
  apply Subtype.ext
  apply Subtype.ext
  exact (cycleRankOneEdge_spec G A).2.symm.trans (hcl.trans (cycleRankOneEdge_spec G B).2)

theorem cycleRankOneToSimpleEdge_surjective : Function.Surjective (cycleRankOneToSimpleEdge G) := by
  intro t
  obtain ⟨e, he, heq⟩ := graphSimpleEdge_has_nonloop G t
  let A : RankOneFlat (cycleMatroid G) := ⟨elementFlat (cycleMatroid G) e.1, elementFlat_rank_one he⟩
  refine ⟨A, Subtype.ext ?_⟩
  change graphEdgeEnds G (cycleRankOneEdge G A) = t.1
  have hcl : (cycleMatroid G).closure {(cycleRankOneEdge G A).1} = (cycleMatroid G).closure {e.1} :=
    (cycleRankOneEdge_spec G A).2
  have hEnds := (cycleMatroid_singleton_closure_eq_iff G (cycleRankOneEdge G A) e
    (cycleRankOneEdge_spec G A).1 he).mp hcl
  exact hEnds.trans heq

/-- Actual rank-one flats (the simplification ground) and actual simple
graph edges are bijective. All original parallel-edge labels are retained
in the inverse class equation below. -/
noncomputable def cycleRankOneEquivSimpleEdges :
    RankOneFlat (cycleMatroid G) ≃ (graphSimplification G).edgeSet :=
  Equiv.ofBijective (cycleRankOneToSimpleEdge G)
    ⟨cycleRankOneToSimpleEdge_injective G, cycleRankOneToSimpleEdge_surjective G⟩

theorem cycleRankOneEquivSimpleEdges_val (A : RankOneFlat (cycleMatroid G)) :
    (cycleRankOneEquivSimpleEdges G A).1 = graphEdgeEnds G (cycleRankOneEdge G A) := rfl

theorem cycleRankOneSimpleEdge_class_member (A : RankOneFlat (cycleMatroid G)) (f : G.edgeSet) :
    f.1 ∈ A.1.1 \ (cycleMatroid G).loops ↔ graphEdgeEnds G f = (cycleRankOneToSimpleEdge G A).1 := by
  rw [← (cycleRankOneEdge_spec G A).2]
  exact cycleMatroid_mem_parallelClass_iff G (cycleRankOneEdge G A) f (cycleRankOneEdge_spec G A).1

/-- Membership in the inverse flat, after removing loops, recovers the
exact original endpoint fibre of the given simple edge. -/
theorem cycleRankOneEquivSimpleEdges_symm_class (t : (graphSimplification G).edgeSet) (f : G.edgeSet) :
    f.1 ∈ ((cycleRankOneEquivSimpleEdges G).symm t).1.1 \ (cycleMatroid G).loops ↔
      graphEdgeEnds G f = t.1 := by
  have h := cycleRankOneSimpleEdge_class_member G ((cycleRankOneEquivSimpleEdges G).symm t) f
  change _ ↔ graphEdgeEnds G f = (cycleRankOneEquivSimpleEdges G ((cycleRankOneEquivSimpleEdges G).symm t)).1 at h
  simpa only [Equiv.apply_symm_apply] using h

end BooleanAntichainsKernel
