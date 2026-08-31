import BooleanAntichainsKernel.CycleMatroidLoops

namespace BooleanAntichainsKernel

open scoped Classical

variable {α β : Type*} (G : Graph α β) [Finite G.vertexSet] [Finite G.edgeSet]

/-- The actual nonloop parallel class is exactly an original unordered
endpoint fibre. The nonloop guard on its representative is discharged by
the rank-one-flat producers before this is used for simplification. -/
theorem cycleMatroid_mem_parallelClass_iff (e f : G.edgeSet) (he : (cycleMatroid G).IsNonloop e.1) :
    f.1 ∈ (cycleMatroid G).closure {e.1} \ (cycleMatroid G).loops ↔
      graphEdgeEnds G f = graphEdgeEnds G e := by
  constructor
  · intro hf
    have hfN : (cycleMatroid G).IsNonloop f.1 := ⟨hf.2, f.2⟩
    have hnd := (cycleMatroid_isNonloop_ends_iff G f).mp hfN
    let uv := (graphEdgeEndpoints G f).1
    have hfl : G.IsLink f.1 uv.1.1 uv.2.1 := (graphEdgeEndpoints G f).2
    have huv : uv.1 ≠ uv.2 := by
      intro h
      apply hnd
      rw [graphEdgeEnds_eq f hfl, Sym2.mk_isDiag_iff]
      exact h
    have hr := (cycleMatroid_mem_closure_iff G {e.1} (Set.singleton_subset_iff.mpr e.2) f hfl).mp hf.1
    rcases (graphReachable_singleton_iff G e uv.1 uv.2).mp hr with heq | hel
    · exact (huv heq).elim
    · exact (graphEdgeEnds_eq f hfl).trans (graphEdgeEnds_eq e hel).symm
  · intro hEnds
    let uv := (graphEdgeEndpoints G e).1
    have hel : G.IsLink e.1 uv.1.1 uv.2.1 := (graphEdgeEndpoints G e).2
    have hfl : G.IsLink f.1 uv.1.1 uv.2.1 :=
      (graphEdgeEnds_eq_iff f uv.1 uv.2).mp (hEnds.trans (graphEdgeEnds_eq e hel))
    have hr : GraphReachable G {e.1} uv.1 uv.2 :=
      ⟨LabelledGraphWalk.cons e (by simp) hel (.nil uv.2)⟩
    have hc := (cycleMatroid_mem_closure_iff G {e.1} (Set.singleton_subset_iff.mpr e.2) f hfl).mpr hr
    have hfN : (cycleMatroid G).IsNonloop f.1 := (cycleMatroid_isNonloop_ends_iff G f).mpr (by
      rw [hEnds]
      exact (cycleMatroid_isNonloop_ends_iff G e).mp he)
    exact ⟨hc, hfN.not_isLoop⟩

/-- Equality on the original ambient edge sets, with no loss of parallel
multiplicity. In particular the representative edge itself remains in the class. -/
theorem cycleMatroid_parallelClass_eq (e : G.edgeSet) (he : (cycleMatroid G).IsNonloop e.1) :
    (cycleMatroid G).closure {e.1} \ (cycleMatroid G).loops =
      {f : β | ∃ x y : α, G.IsLink e.1 x y ∧ G.IsLink f x y} := by
  ext f
  constructor
  · intro hf
    have hfG : f ∈ G.edgeSet := (cycleMatroid G).closure_subset_ground {e.1} hf.1
    have hEnds := (cycleMatroid_mem_parallelClass_iff G e ⟨f, hfG⟩ he).mp hf
    exact (graphEdgeEnds_eq_iff_same_link G e ⟨f, hfG⟩).mp hEnds.symm
  · rintro ⟨x, y, hel, hfl⟩
    have hEnds := (graphEdgeEnds_eq_iff_same_link G e ⟨f, hfl.edge_mem⟩).mpr ⟨x, y, hel, hfl⟩
    exact (cycleMatroid_mem_parallelClass_iff G e ⟨f, hfl.edge_mem⟩ he).mpr hEnds.symm

theorem cycleMatroid_singleton_closure_eq_iff (e f : G.edgeSet)
    (he : (cycleMatroid G).IsNonloop e.1) (hf : (cycleMatroid G).IsNonloop f.1) :
    (cycleMatroid G).closure {e.1} = (cycleMatroid G).closure {f.1} ↔
      graphEdgeEnds G e = graphEdgeEnds G f := by
  constructor
  · intro h
    have hem : e.1 ∈ (cycleMatroid G).closure {f.1} := by
      rw [← h]
      exact (cycleMatroid G).mem_closure_self e.1 e.2
    exact (cycleMatroid_mem_parallelClass_iff G f e hf).mp ⟨hem, he.not_isLoop⟩
  · intro h
    have hem := ((cycleMatroid_mem_parallelClass_iff G f e hf).mpr h).1
    have hfm := ((cycleMatroid_mem_parallelClass_iff G e f he).mpr h.symm).1
    exact Set.Subset.antisymm
      ((cycleMatroid G).closure_subset_closure_of_subset_closure (Set.singleton_subset_iff.mpr hem))
      ((cycleMatroid G).closure_subset_closure_of_subset_closure (Set.singleton_subset_iff.mpr hfm))

end BooleanAntichainsKernel
