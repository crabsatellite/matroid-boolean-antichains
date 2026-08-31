import BooleanAntichainsKernel.CycleMatroidParallel
import BooleanAntichainsKernel.MatroidSimplification
import BooleanAntichainsKernel.ParallelClasses

namespace BooleanAntichainsKernel

open scoped Classical

variable {α β : Type*} (G : Graph α β) [Finite G.vertexSet] [Finite G.edgeSet]

/-- Obtain an original nonloop edge from an actual one-element basis of
the actual rank-one flat. No ambient-edge Fintype premise is required. -/
theorem cycleRankOne_has_edge (A : RankOneFlat (cycleMatroid G)) :
    ∃ e : G.edgeSet, (cycleMatroid G).IsNonloop e.1 ∧ (cycleMatroid G).closure {e.1} = A.1.1 := by
  obtain ⟨I, hI⟩ := (cycleMatroid G).exists_isBasis A.1.1 A.1.2.subset_ground
  have hr : matroidRank (cycleMatroid G) A.1.1 = I.ncard := by
    change ((cycleMatroid G).eRk A.1.1).toNat = I.ncard
    rw [hI.eRk_eq_encard]
    rfl
  have hc : I.ncard = 1 := hr.symm.trans A.2
  obtain ⟨e, hIe⟩ := Set.ncard_eq_one.mp hc
  have hS : (cycleMatroid G).Indep {e} := hIe ▸ hI.indep
  have hN := hS.isNonloop
  refine ⟨⟨e, hN.mem_ground⟩, hN, ?_⟩
  have hcl := hI.closure_eq_closure.trans A.1.2.closure
  simpa only [hIe] using hcl

noncomputable def cycleRankOneEdge (A : RankOneFlat (cycleMatroid G)) : G.edgeSet :=
  (cycleRankOne_has_edge G A).choose

theorem cycleRankOneEdge_spec (A : RankOneFlat (cycleMatroid G)) :
    (cycleMatroid G).IsNonloop (cycleRankOneEdge G A).1 ∧
      (cycleMatroid G).closure {(cycleRankOneEdge G A).1} = A.1.1 :=
  (cycleRankOne_has_edge G A).choose_spec

noncomputable def cycleNonloopToSimpleEdge (e : G.edgeSet) (he : (cycleMatroid G).IsNonloop e.1) :
    (graphSimplification G).edgeSet := by
  refine ⟨graphEdgeEnds G e, ?_⟩
  change graphEdgeEnds G e ∈ (graphSupport G G.edgeSet).edgeSet
  rw [graphSupport_edgeSet]
  exact ⟨⟨e, e.2, rfl⟩, (cycleMatroid_isNonloop_ends_iff G e).mp he⟩

theorem cycleNonloopToSimpleEdge_val (e : G.edgeSet) (he : (cycleMatroid G).IsNonloop e.1) :
    (cycleNonloopToSimpleEdge G e he).1 = graphEdgeEnds G e := rfl

noncomputable def cycleRankOneToSimpleEdge (A : RankOneFlat (cycleMatroid G)) :
    (graphSimplification G).edgeSet :=
  cycleNonloopToSimpleEdge G (cycleRankOneEdge G A) (cycleRankOneEdge_spec G A).1

theorem cycleRankOneToSimpleEdge_val (A : RankOneFlat (cycleMatroid G)) :
    (cycleRankOneToSimpleEdge G A).1 = graphEdgeEnds G (cycleRankOneEdge G A) := rfl

/-- The full original parallel class represented by the output simple
edge is the actual rank-one flat minus the actual loop flat. -/
theorem cycleRankOne_class_eq (A : RankOneFlat (cycleMatroid G)) :
    A.1.1 \ (cycleMatroid G).loops =
      {f : β | ∃ x y : α, G.IsLink (cycleRankOneEdge G A).1 x y ∧ G.IsLink f x y} := by
  rw [← (cycleRankOneEdge_spec G A).2]
  exact cycleMatroid_parallelClass_eq G (cycleRankOneEdge G A) (cycleRankOneEdge_spec G A).1

end BooleanAntichainsKernel
