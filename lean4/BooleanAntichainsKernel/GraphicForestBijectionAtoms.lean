import BooleanAntichainsKernel.GraphicForestBijection
import BooleanAntichainsKernel.GraphicSpanEdges

namespace BooleanAntichainsKernel

open scoped Classical

variable {α β : Type*} (G : Graph α β) [Finite G.vertexSet] [Finite G.edgeSet]

attribute [local instance] cycleMatroidGroundFintype
attribute [local instance 100] matroidGroundFlatFintype matroidGroundBasesFintype

local notation "N" => Matroid.restrictSubtype (cycleMatroid G) (Matroid.E (cycleMatroid G))

theorem graphicGroundSpanEdge_mem (D : MaximumBooleanAntichain N) (A : RankOneFlat N) :
    graphicGroundRankOneEquiv G A ∈
      graphMaximumSpanEdges G (matroidGroundMaximumEquiv (cycleMatroid G) D) ↔
        A.1 ∈ antichainAtoms D.1 := by
  rw [graphMaximumSpanEdges_mem, matroidGroundMaximumEquiv_spanAtoms]
  have hA : (cycleRankOneEquivSimpleEdges G).symm (graphicGroundRankOneEquiv G A) =
      matroidGroundRankOneEquiv (cycleMatroid G) A :=
    (cycleRankOneEquivSimpleEdges G).symm_apply_apply (matroidGroundRankOneEquiv (cycleMatroid G) A)
  rw [hA, spanAtomFinset_eq_antichainAtoms D.1 D.2.2]
  change (matroidGroundFlatOrderIso (cycleMatroid G)).toEquiv.toEmbedding A.1 ∈
    (antichainAtoms D.1).map (matroidGroundFlatOrderIso (cycleMatroid G)).toEquiv.toEmbedding ↔ _
  exact Finset.mem_map' _

theorem graphicMaximumAntichainEquivForests_ground_val (D : MaximumBooleanAntichain N) :
    (graphicMaximumAntichainEquivForests G (matroidGroundMaximumEquiv (cycleMatroid G) D)).1 =
      (liftRankOneFamily (antichainAtoms D.1)).map
        ⟨graphicGroundSimpleLabel G, graphicGroundSimpleLabel_injective G⟩ := by
  change (graphicSimplificationBasesEquivForests G
    (simplifiedBasisEquivActualMatroidBases (maximumAntichainEquivSimplifiedBasis
      ((matroidGroundMaximumEquiv (cycleMatroid G)).symm
        (matroidGroundMaximumEquiv (cycleMatroid G) D))))).1 = _
  rw [Equiv.symm_apply_apply, graphicSimplificationBasesEquivForests_val]
  rfl

/-- The bijection outputs exactly the simple edges of the literal span
atoms. This identifies the forest map with the weighted theorem's map. -/
theorem graphicMaximumAntichainEquivForests_val
    (C : BooleanAntichain (MatroidFlat.rank (⊤ : MatroidFlat (cycleMatroid G)))
      (MatroidFlat (cycleMatroid G))) :
    (graphicMaximumAntichainEquivForests G C).1 =
      (graphMaximumSpanEdges G C).map (Function.Embedding.subtype _) := by
  obtain ⟨D, rfl⟩ := (matroidGroundMaximumEquiv (cycleMatroid G)).surjective C
  rw [graphicMaximumAntichainEquivForests_ground_val]
  ext q
  constructor
  · intro hq
    rcases Finset.mem_map.mp hq with ⟨A, hA, hAq⟩
    have ha : A.1 ∈ antichainAtoms D.1 := (Finset.mem_filter.mp hA).2
    exact Finset.mem_map.mpr ⟨graphicGroundRankOneEquiv G A,
      (graphicGroundSpanEdge_mem G D A).mpr ha, hAq⟩
  · intro hq
    rcases Finset.mem_map.mp hq with ⟨t, ht, htq⟩
    obtain ⟨A, rfl⟩ := (graphicGroundRankOneEquiv G).surjective t
    have ha := (graphicGroundSpanEdge_mem G D A).mp ht
    exact Finset.mem_map.mpr ⟨A, Finset.mem_filter.mpr ⟨Finset.mem_univ A, ha⟩, htq⟩

theorem graphMaximumSpanEdges_spanningForest
    (C : BooleanAntichain (MatroidFlat.rank (⊤ : MatroidFlat (cycleMatroid G)))
      (MatroidFlat (cycleMatroid G))) :
    GraphSpanningForest (graphSimplifiedGraph G)
      (↑((graphMaximumSpanEdges G C).map (Function.Embedding.subtype _)) : Set (Sym2 G.vertexSet)) := by
  rw [← graphicMaximumAntichainEquivForests_val]
  exact (graphicMaximumAntichainEquivForests G C).2

theorem graphMaximumSpanEdges_card
    (C : BooleanAntichain (MatroidFlat.rank (⊤ : MatroidFlat (cycleMatroid G)))
      (MatroidFlat (cycleMatroid G))) :
    (graphMaximumSpanEdges G C).card = G.vertexSet.ncard - graphConnectedComponentCount G := by
  have h := graphSpanningForest_card (graphSimplifiedGraph G) (graphicMaximumAntichainEquivForests G C)
  rw [graphicMaximumAntichainEquivForests_val, Finset.card_map,
    graphSimplifiedGraph_component_count] at h
  exact h

end BooleanAntichainsKernel
