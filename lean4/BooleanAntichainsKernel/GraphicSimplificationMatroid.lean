import BooleanAntichainsKernel.GraphicSimplificationRepresentatives

namespace BooleanAntichainsKernel

open scoped Classical

variable {α β : Type*} (G : Graph α β) [Finite G.vertexSet] [Finite G.edgeSet]

attribute [local instance] cycleMatroidGroundFintype

local notation "N" => Matroid.restrictSubtype (cycleMatroid G) (Matroid.E (cycleMatroid G))

theorem graphicGroundOriginalLabel_image_no_loops (X : Set (RankOneFlat N)) :
    ∀ e ∈ graphicGroundOriginalLabel G '' X, ∀ x : α, ¬G.IsLoopAt e x := by
  rintro e ⟨A, _hA, rfl⟩ x hx
  exact (graphicGroundRepresentative_in_class G A).2
    ((cycleMatroid_isLoop_iff G _).mpr ⟨x, hx⟩)

theorem graphicGroundOriginalLabel_ends_injOn (X : Set (RankOneFlat N)) :
    Set.InjOn (graphEdgeEnds G) {e : G.edgeSet | e.1 ∈ graphicGroundOriginalLabel G '' X} := by
  rintro e ⟨A, _hA, hAe⟩ f ⟨B, _hB, hBf⟩ h
  have ha : graphicGroundRepresentative G A = e := Subtype.ext hAe
  have hb : graphicGroundRepresentative G B = f := Subtype.ext hBf
  rw [← ha, ← hb, graphicGroundRepresentative_ends, graphicGroundRepresentative_ends] at h
  have hAB := graphicGroundSimpleLabel_injective G h
  subst B
  exact ha.symm.trans hb

theorem graphicGroundOriginalLabel_forest_iff (X : Set (RankOneFlat N)) :
    GraphEdgeForest G (graphicGroundOriginalLabel G '' X) ↔
      (SimpleGraph.fromEdgeSet (graphicGroundSimpleLabel G '' X)).IsAcyclic := by
  constructor
  · intro hF
    exact (graphicGroundRepresentative_support G X) ▸ hF.support_isAcyclic
  · intro hA
    exact graphEdgeForest_iff_support.mpr
      ⟨graphicGroundOriginalLabel_image_ground G X, graphicGroundOriginalLabel_image_no_loops G X,
        graphicGroundOriginalLabel_ends_injOn G X,
        (graphicGroundRepresentative_support G X).symm ▸ hA⟩

/-- Translate the existing representative-comap simplification literally,
then consume the proved original-support equality. -/
theorem graphic_simplification_indep_support (X : Set (RankOneFlat N)) :
    (simplificationOnFlats N).Indep X ↔
      (SimpleGraph.fromEdgeSet (graphicGroundSimpleLabel G '' X)).IsAcyclic := by
  rw [simplificationOnFlats, Matroid.comap_indep_iff, Matroid.restrictSubtype_indep_iff,
    Set.image_image]
  change (GraphEdgeForest G (graphicGroundOriginalLabel G '' X) ∧
    Set.InjOn (rankOneRepresentative (M := N)) X) ↔ _
  exact (and_iff_left (rankOneRepresentative_injective (M := N)).injOn).trans
    (graphicGroundOriginalLabel_forest_iff G X)

theorem graphic_simplification_indep (X : Set (RankOneFlat N)) :
    (simplificationOnFlats N).Indep X ↔
      (cycleMatroid (graphSimplifiedGraph G)).Indep (graphicGroundSimpleLabel G '' X) := by
  rw [graphSimplifiedGraph_cycleMatroid_indep]
  exact (graphic_simplification_indep_support G X).trans
    (and_iff_right (graphicGroundSimpleLabel_image_ground G X)).symm

theorem graphicGroundSimpleLabel_preimage_ground :
    graphicGroundSimpleLabel G ⁻¹' (cycleMatroid (graphSimplifiedGraph G)).E = Set.univ := by
  ext A
  exact iff_of_true (graphicGroundRankOneEquiv G A).2 (Set.mem_univ A)

/-- Equality of actual mathlib matroids after the proved bijective ground
transport. All independent sets are identified, not only their ranks or bases. -/
theorem graphic_simplification_eq_comap :
    simplificationOnFlats N =
      (cycleMatroid (graphSimplifiedGraph G)).comap (graphicGroundSimpleLabel G) := by
  apply Matroid.ext_indep
  · rw [simplificationOnFlats_ground, Matroid.comap_ground_eq,
      graphicGroundSimpleLabel_preimage_ground]
  · intro X _hX
    rw [Matroid.comap_indep_iff]
    exact (graphic_simplification_indep G X).trans
      (and_iff_left (graphicGroundSimpleLabel_injective G).injOn).symm

theorem graphic_simplification_isBase (B : Set (RankOneFlat N)) :
    (simplificationOnFlats N).IsBase B ↔
      (cycleMatroid (graphSimplifiedGraph G)).IsBase (graphicGroundSimpleLabel G '' B) := by
  rw [graphic_simplification_eq_comap, Matroid.comap_isBase_iff,
    graphicGroundSimpleLabel_preimage_ground, Set.image_univ, graphicGroundSimpleLabel_range]
  change ((cycleMatroid (graphSimplifiedGraph G)).IsBasis (graphicGroundSimpleLabel G '' B)
    (cycleMatroid (graphSimplifiedGraph G)).E ∧
    Set.InjOn (graphicGroundSimpleLabel G) B ∧ B ⊆ Set.univ) ↔ _
  rw [Matroid.isBasis_ground_iff]
  simp only [Set.subset_univ, and_true, (graphicGroundSimpleLabel_injective G).injOn,
    and_true]

/-- The main theorem's simplification bases now correspond to the native
simplified graph's literal one-tree-per-component spanning forests. -/
theorem graphic_simplification_base_spanningForest (B : Set (RankOneFlat N)) :
    (simplificationOnFlats N).IsBase B ↔
      GraphSpanningForest (graphSimplifiedGraph G) (graphicGroundSimpleLabel G '' B) :=
  (graphic_simplification_isBase G B).trans
    (cycleMatroid_isBase_iff_spanningForest (graphSimplifiedGraph G) _)

end BooleanAntichainsKernel
