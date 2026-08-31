import BooleanAntichainsKernel.GraphicWeights

namespace BooleanAntichainsKernel

open scoped Classical

variable {α β R : Type*} (G : Graph α β) [Finite G.vertexSet] [Finite G.edgeSet]

attribute [local instance] cycleMatroidGroundFintype
attribute [local instance 100] matroidGroundFlatFintype matroidGroundBasesFintype

/-- Send each literal Boolean-span atom to its actual simplified graph edge. -/
noncomputable def graphSpanAtomEdge
    (C : BooleanAntichain (MatroidFlat.rank (⊤ : MatroidFlat (cycleMatroid G)))
      (MatroidFlat (cycleMatroid G))) (A : spanAtomFinset C.1) :
    (graphSimplification G).edgeSet :=
  cycleRankOneEquivSimpleEdges G ⟨A.1, graphMaximumAntichain_spanAtom_rank G C A.1 A.2⟩

theorem graphSpanAtomEdge_injective
    (C : BooleanAntichain (MatroidFlat.rank (⊤ : MatroidFlat (cycleMatroid G)))
      (MatroidFlat (cycleMatroid G))) : Function.Injective (graphSpanAtomEdge G C) := by
  intro A B h
  have hAB := (cycleRankOneEquivSimpleEdges G).injective h
  exact Subtype.ext (congrArg (fun F : RankOneFlat (cycleMatroid G) ↦ F.1) hAB)

noncomputable def graphMaximumSpanEdges
    (C : BooleanAntichain (MatroidFlat.rank (⊤ : MatroidFlat (cycleMatroid G)))
      (MatroidFlat (cycleMatroid G))) : Finset (graphSimplification G).edgeSet :=
  (spanAtomFinset C.1).attach.map ⟨graphSpanAtomEdge G C, graphSpanAtomEdge_injective G C⟩

theorem graphMaximumSpanEdges_mem
    (C : BooleanAntichain (MatroidFlat.rank (⊤ : MatroidFlat (cycleMatroid G)))
      (MatroidFlat (cycleMatroid G))) (t : (graphSimplification G).edgeSet) :
    t ∈ graphMaximumSpanEdges G C ↔
      ((cycleRankOneEquivSimpleEdges G).symm t).1 ∈ spanAtomFinset C.1 := by
  constructor
  · intro ht
    rcases Finset.mem_map.mp ht with ⟨A, _hA, hAt⟩
    have h := (cycleRankOneEquivSimpleEdges G).symm_apply_apply
      (⟨A.1, graphMaximumAntichain_spanAtom_rank G C A.1 A.2⟩ : RankOneFlat (cycleMatroid G))
    change graphSpanAtomEdge G C A = t at hAt
    change (cycleRankOneEquivSimpleEdges G).symm (graphSpanAtomEdge G C A) = _ at h
    rw [hAt] at h
    exact (congrArg (fun F : RankOneFlat (cycleMatroid G) ↦ F.1) h).symm ▸ A.2
  · intro ht
    let A : spanAtomFinset C.1 := ⟨((cycleRankOneEquivSimpleEdges G).symm t).1, ht⟩
    refine Finset.mem_map.mpr ⟨A, Finset.mem_attach _ _, ?_⟩
    change graphSpanAtomEdge G C A = t
    exact (cycleRankOneEquivSimpleEdges G).apply_symm_apply t

theorem graphMaximumSpanEdges_class
    (C : BooleanAntichain (MatroidFlat.rank (⊤ : MatroidFlat (cycleMatroid G)))
      (MatroidFlat (cycleMatroid G))) (A : spanAtomFinset C.1) :
    graphParallelEdgeClass G (graphSpanAtomEdge G C A) =
      matroidGroundParallelClassElements (cycleMatroid G) A.1 :=
  graphParallelEdgeClass_eq_rankOne G
    ⟨A.1, graphMaximumAntichain_spanAtom_rank G C A.1 A.2⟩

theorem graphMaximumSpanEdges_weight [CommSemiring R]
    (C : BooleanAntichain (MatroidFlat.rank (⊤ : MatroidFlat (cycleMatroid G)))
      (MatroidFlat (cycleMatroid G))) (x : β → R) :
    (∏ t ∈ graphMaximumSpanEdges G C, ∑ e ∈ graphParallelEdgeClass G t, x e) =
      ∏ A ∈ spanAtomFinset C.1, ∑ e ∈ matroidGroundParallelClassElements (cycleMatroid G) A, x e := by
  rw [graphMaximumSpanEdges, Finset.prod_map]
  change (∏ A ∈ (spanAtomFinset C.1).attach,
    ∑ e ∈ graphParallelEdgeClass G (graphSpanAtomEdge G C A), x e) = _
  simp_rw [graphMaximumSpanEdges_class]
  exact Finset.prod_attach (spanAtomFinset C.1)
    (fun A ↦ ∑ e ∈ matroidGroundParallelClassElements (cycleMatroid G) A, x e)

/-- Each simplified edge contributes the sum of all original variables
in its exact endpoint fibre; the injective atom map earns the product. -/
theorem graphic_weighted_parallel_edge_expansion [CommSemiring R] (x : β → R) :
    (∑ F : GraphSpanningForests G, ∏ e ∈ F.1, x e) =
      ∑ C : BooleanAntichain (MatroidFlat.rank (⊤ : MatroidFlat (cycleMatroid G)))
          (MatroidFlat (cycleMatroid G)),
        ∏ t ∈ graphMaximumSpanEdges G C, ∑ e ∈ graphParallelEdgeClass G t, x e := by
  simp_rw [graphMaximumSpanEdges_weight]
  exact graphSpanningForestWeight_sum G x

theorem graphic_spanningForestPolynomial_parallel_edge_expansion :
    graphSpanningForestPolynomial G =
      ∑ C : BooleanAntichain (MatroidFlat.rank (⊤ : MatroidFlat (cycleMatroid G)))
          (MatroidFlat (cycleMatroid G)),
        ∏ t ∈ graphMaximumSpanEdges G C, ∑ e ∈ graphParallelEdgeClass G t,
          (MvPolynomial.X e : MvPolynomial β ℤ) :=
  graphic_weighted_parallel_edge_expansion G MvPolynomial.X

end BooleanAntichainsKernel
