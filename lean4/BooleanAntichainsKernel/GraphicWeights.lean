import BooleanAntichainsKernel.MatroidGroundWeights
import BooleanAntichainsKernel.CycleMatroidForests
import BooleanAntichainsKernel.GraphicSimplificationGround

namespace BooleanAntichainsKernel

open scoped Classical

variable {α β R : Type*}

@[implicit_reducible] noncomputable def cycleMatroidGroundFintype (G : Graph α β)
    [Finite G.vertexSet] [Finite G.edgeSet] : Fintype (cycleMatroid G).E :=
  Fintype.ofFinite G.edgeSet

attribute [local instance] cycleMatroidGroundFintype
attribute [local instance 100] matroidGroundFlatFintype matroidGroundBasesFintype

/-- The complete original-edge fibre of a simplified edge, defined by
actual graph links and not by a chosen representative. -/
noncomputable def graphParallelEdgeClass (G : Graph α β) [Finite G.edgeSet]
    (t : (graphSimplification G).edgeSet) : Finset β :=
  ((Set.toFinite G.edgeSet).subset (fun _ he ↦ by
    obtain ⟨x, y, _ht, hlink⟩ := he
    exact hlink.edge_mem :
    {e : β | ∃ x y : G.vertexSet, t.1 = s(x, y) ∧ G.IsLink e x.1 y.1} ⊆ G.edgeSet)).toFinset

theorem graphParallelEdgeClass_mem (G : Graph α β) [Finite G.edgeSet]
    (t : (graphSimplification G).edgeSet) (e : β) :
    e ∈ graphParallelEdgeClass G t ↔
      ∃ x y : G.vertexSet, t.1 = s(x, y) ∧ G.IsLink e x.1 y.1 :=
  Set.Finite.mem_toFinset _

theorem graphParallelEdgeClass_mem_ends (G : Graph α β) [Finite G.edgeSet]
    (t : (graphSimplification G).edgeSet) (e : G.edgeSet) :
    e.1 ∈ graphParallelEdgeClass G t ↔ graphEdgeEnds G e = t.1 := by
  rw [graphParallelEdgeClass_mem]
  constructor
  · rintro ⟨x, y, ht, hl⟩
    exact (graphEdgeEnds_eq e hl).trans ht.symm
  · intro he
    let uv := (graphEdgeEndpoints G e).1
    have hl : G.IsLink e.1 uv.1.1 uv.2.1 := (graphEdgeEndpoints G e).2
    exact ⟨uv.1, uv.2, he.symm.trans (graphEdgeEnds_eq e hl), hl⟩

theorem graphParallelEdgeClass_eq_rankOne (G : Graph α β)
    [Finite G.vertexSet] [Finite G.edgeSet] (A : RankOneFlat (cycleMatroid G)) :
    graphParallelEdgeClass G (cycleRankOneEquivSimpleEdges G A) =
      matroidGroundParallelClassElements (cycleMatroid G) A.1 := by
  ext e
  rw [matroidGroundParallelClassElements_mem]
  constructor
  · intro he
    obtain ⟨x, y, _ht, hl⟩ := (graphParallelEdgeClass_mem G _ e).mp he
    have hh := (graphParallelEdgeClass_mem_ends G _ ⟨e, hl.edge_mem⟩).mp he
    exact (cycleRankOneSimpleEdge_class_member G A ⟨e, hl.edge_mem⟩).mpr hh
  · intro he
    have heG : e ∈ G.edgeSet := A.1.2.subset_ground he.1
    apply (graphParallelEdgeClass_mem_ends G _ ⟨e, heG⟩).mpr
    exact (cycleRankOneSimpleEdge_class_member G A ⟨e, heG⟩).mp he

theorem graphSpanningForestWeight_sum [CommSemiring R] (G : Graph α β)
    [Finite G.vertexSet] [Finite G.edgeSet] (x : β → R) :
    (∑ F : GraphSpanningForests G, ∏ e ∈ F.1, x e) =
      ∑ C : BooleanAntichain (MatroidFlat.rank (⊤ : MatroidFlat (cycleMatroid G)))
          (MatroidFlat (cycleMatroid G)),
        ∏ A ∈ spanAtomFinset C.1,
          ∑ e ∈ matroidGroundParallelClassElements (cycleMatroid G) A, x e := by
  calc
    _ = ∑ B : MatroidBases (cycleMatroid G), ∏ e ∈ B.1, x e := by
      have h := (cycleMatroidBasesEquivSpanningForests G).sum_comp
        (fun F : GraphSpanningForests G ↦ ∏ e ∈ F.1, x e)
      simpa only [cycleMatroidBasesEquivSpanningForests_val] using h.symm
    _ = _ := finiteGround_weighted_basis_sum (cycleMatroid G) x

/-- Defined directly by the paper's original labelled spanning forests. -/
noncomputable def graphSpanningForestPolynomial (G : Graph α β) [Finite G.edgeSet] :
    MvPolynomial β ℤ :=
  ∑ F : GraphSpanningForests G, ∏ e ∈ F.1, MvPolynomial.X e

theorem graphSpanningForestPolynomial_eq (G : Graph α β)
    [Finite G.vertexSet] [Finite G.edgeSet] :
    graphSpanningForestPolynomial G =
      ∑ C : BooleanAntichain (MatroidFlat.rank (⊤ : MatroidFlat (cycleMatroid G)))
          (MatroidFlat (cycleMatroid G)),
        ∏ A ∈ spanAtomFinset C.1,
          ∑ e ∈ matroidGroundParallelClassElements (cycleMatroid G) A,
            (MvPolynomial.X e : MvPolynomial β ℤ) :=
  graphSpanningForestWeight_sum G MvPolynomial.X

theorem graphMaximumAntichain_card (G : Graph α β)
    [Finite G.vertexSet] [Finite G.edgeSet]
    (C : BooleanAntichain (MatroidFlat.rank (⊤ : MatroidFlat (cycleMatroid G)))
      (MatroidFlat (cycleMatroid G))) :
    C.1.card = G.vertexSet.ncard - graphConnectedComponentCount G :=
  C.2.1.trans (cycleMatroid_rank G)

/-- Actual span atoms are rank-one original flats, so the class equation
above applies to every factor in the graph polynomial. -/
theorem graphMaximumAntichain_spanAtom_rank (G : Graph α β)
    [Finite G.vertexSet] [Finite G.edgeSet]
    (C : BooleanAntichain (MatroidFlat.rank (⊤ : MatroidFlat (cycleMatroid G)))
      (MatroidFlat (cycleMatroid G)))
    (A : MatroidFlat (cycleMatroid G)) (hA : A ∈ spanAtomFinset C.1) :
    MatroidFlat.rank A = 1 := by
  obtain ⟨D, rfl⟩ := (matroidGroundMaximumEquiv (cycleMatroid G)).surjective C
  rw [matroidGroundMaximumEquiv_spanAtoms] at hA
  rcases Finset.mem_map.mp hA with ⟨B, hB, rfl⟩
  rw [spanAtomFinset_eq_antichainAtoms D.1 D.2.2] at hB
  change MatroidFlat.rank (matroidGroundFlatOrderIso (cycleMatroid G) B) = 1
  rw [matroidGroundFlatOrderIso_rank]
  exact (maximumAntichain_atoms_isSimplifiedBasis D).1 B hB

end BooleanAntichainsKernel
