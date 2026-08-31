import BooleanAntichainsKernel.GraphicSimplificationMatroid
import BooleanAntichainsKernel.SimplificationBases

namespace BooleanAntichainsKernel

open scoped Classical

variable {α β : Type*} (G : Graph α β) [Finite G.vertexSet] [Finite G.edgeSet]

attribute [local instance] cycleMatroidGroundFintype
attribute [local instance 100] matroidGroundFlatFintype matroidGroundBasesFintype

local notation "N" => Matroid.restrictSubtype (cycleMatroid G) (Matroid.E (cycleMatroid G))
local notation "S" => graphSimplifiedGraph G
local notation "Q" => cycleMatroid (graphSimplifiedGraph G)

noncomputable def graphicSimplificationBasesEquivGround :
    MatroidBases (simplificationOnFlats N) ≃ MatroidBases (Matroid.restrictSubtype Q (Matroid.E Q)) :=
  Equiv.subtypeEquiv (graphicGroundRankOneEquiv G).finsetCongr (fun B ↦ by
    rw [Matroid.restrictSubtype_ground_isBase_iff]
    change _ ↔ (Q).IsBase ((Subtype.val : (graphSimplification G).edgeSet → Sym2 G.vertexSet) ''
      (↑((graphicGroundRankOneEquiv G).finsetCongr B) : Set (graphSimplification G).edgeSet))
    rw [Equiv.finsetCongr_apply, Finset.coe_map, Set.image_image]
    exact graphic_simplification_isBase G (B : Set (RankOneFlat N)))

/-- Compose actual ground transport and the literal base/forest map. -/
noncomputable def graphicSimplificationBasesEquivForests :
    MatroidBases (simplificationOnFlats N) ≃ GraphSpanningForests S :=
  (graphicSimplificationBasesEquivGround G).trans
    ((matroidGroundBasesEquiv Q).trans (cycleMatroidBasesEquivSpanningForests S))

theorem graphicSimplificationBasesEquivForests_val (B : MatroidBases (simplificationOnFlats N)) :
    (graphicSimplificationBasesEquivForests G B).1 =
      B.1.map ⟨graphicGroundSimpleLabel G, graphicGroundSimpleLabel_injective G⟩ := by
  change (B.1.map (graphicGroundRankOneEquiv G).toEmbedding).map (Function.Embedding.subtype _) = _
  rw [Finset.map_map]
  rfl

/-- The manuscript's maximum-antichain / simplified spanning-forest
bijection. Each constituent map has proved inverse laws on literal carriers. -/
noncomputable def graphicMaximumAntichainEquivForests :
    BooleanAntichain (MatroidFlat.rank (⊤ : MatroidFlat (cycleMatroid G)))
      (MatroidFlat (cycleMatroid G)) ≃ GraphSpanningForests S :=
  (matroidGroundMaximumEquiv (cycleMatroid G)).symm.trans
    (maximumAntichainEquivSimplifiedBasis.trans
      (simplifiedBasisEquivActualMatroidBases.trans (graphicSimplificationBasesEquivForests G)))

theorem graphicMaximumAntichainEquivForests_bijective :
    Function.Bijective (graphicMaximumAntichainEquivForests G) :=
  (graphicMaximumAntichainEquivForests G).bijective

theorem graphicMaximumAntichainEquivForests_left_inv
    (C : BooleanAntichain (MatroidFlat.rank (⊤ : MatroidFlat (cycleMatroid G)))
      (MatroidFlat (cycleMatroid G))) :
    (graphicMaximumAntichainEquivForests G).symm (graphicMaximumAntichainEquivForests G C) = C :=
  (graphicMaximumAntichainEquivForests G).symm_apply_apply C

theorem graphicMaximumAntichainEquivForests_right_inv (F : GraphSpanningForests S) :
    graphicMaximumAntichainEquivForests G ((graphicMaximumAntichainEquivForests G).symm F) = F :=
  (graphicMaximumAntichainEquivForests G).apply_symm_apply F

theorem graphicMaximumAntichain_count :
    Fintype.card (BooleanAntichain (MatroidFlat.rank (⊤ : MatroidFlat (cycleMatroid G)))
      (MatroidFlat (cycleMatroid G))) = Fintype.card (GraphSpanningForests S) :=
  Fintype.card_congr (graphicMaximumAntichainEquivForests G)

end BooleanAntichainsKernel
