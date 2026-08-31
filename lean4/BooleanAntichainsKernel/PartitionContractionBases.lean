import BooleanAntichainsKernel.PartitionSimplification

namespace BooleanAntichainsKernel

open scoped Classical Matroid

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (P : Finpartition (Finset.univ : Finset α))

local notation "A" => Matroid.contract (cycleMatroid (completeLabelledGraph α))
  (Subtype.val (finitePartitionCompleteFlatOrderIso P))
local notation "B" => cycleMatroid (completeLabelledGraph (Finpartition.parts P))

theorem partitionSimplification_isBase (X : Set (RankOneFlat A)) :
    (simplificationOnFlats A).IsBase X ↔ (B).IsBase (partitionSimplificationLabel P '' X) := by
  rw [partition_simplification_eq_comap, Matroid.comap_isBase_iff,
    partitionSimplificationLabel_preimage_ground, Set.image_univ, partitionSimplificationLabel_range]
  rw [Matroid.isBasis_ground_iff]
  exact and_iff_left ⟨(partitionSimplificationLabel_injective P).injOn, Set.subset_univ X⟩

noncomputable def partitionSimplificationBasesGroundEquiv :
    MatroidBases (simplificationOnFlats A) ≃
      MatroidBases (Matroid.restrictSubtype B (Matroid.E B)) :=
  Equiv.subtypeEquiv (partitionSimplificationEdgeEquiv P).finsetCongr (fun I ↦ by
    rw [Matroid.restrictSubtype_ground_isBase_iff]
    change _ ↔ (B).IsBase
      ((Subtype.val : (completeLabelledGraph P.parts).edgeSet → Sym2 P.parts) ''
        (↑((partitionSimplificationEdgeEquiv P).finsetCongr I) : Set (completeLabelledGraph P.parts).edgeSet))
    rw [Equiv.finsetCongr_apply, Finset.coe_map, Set.image_image]
    exact partitionSimplification_isBase P (I : Set (RankOneFlat A)))

/-- The actual contraction-simplification bases and actual complete-graph
bases on original blocks, with both finite-set inverse laws inherited
from the checked ground equivalences. -/
noncomputable def partitionSimplificationBasesEquiv :
    MatroidBases (simplificationOnFlats A) ≃ MatroidBases B :=
  (partitionSimplificationBasesGroundEquiv P).trans (matroidGroundBasesEquiv B)

theorem partitionSimplificationBasesEquiv_val (I : MatroidBases (simplificationOnFlats A)) :
    (partitionSimplificationBasesEquiv P I).1 =
      I.1.map ⟨partitionSimplificationLabel P, partitionSimplificationLabel_injective P⟩ := by
  change (I.1.map (partitionSimplificationEdgeEquiv P).toEmbedding).map (Function.Embedding.subtype _) = _
  rw [Finset.map_map]
  rfl

theorem partitionSimplificationBases_count :
    Fintype.card (MatroidBases (simplificationOnFlats A)) = Fintype.card (MatroidBases B) :=
  Fintype.card_congr (partitionSimplificationBasesEquiv P)

variable [Nonempty α]

local instance : Nonempty P.parts := Nonempty.map (finitePartitionBlockOf P) inferInstance

noncomputable def partitionContractionBasesEquivTrees :
    MatroidBases (simplificationOnFlats A) ≃ GraphSpanningTrees (completeLabelledGraph P.parts) :=
  (partitionSimplificationBasesEquiv P).trans
    ((cycleMatroidBasesEquivSpanningForests (completeLabelledGraph P.parts)).trans
      (graphSpanningForestsEquivTrees (completeLabelledGraph P.parts) completeLabelledGraph_connected))

theorem partitionContractionBasesEquivTrees_val (I : MatroidBases (simplificationOnFlats A)) :
    (partitionContractionBasesEquivTrees P I).1 =
      I.1.map ⟨partitionSimplificationLabel P, partitionSimplificationLabel_injective P⟩ :=
  partitionSimplificationBasesEquiv_val P I

theorem partition_contraction_simplification_tree_count :
    Fintype.card (MatroidBases (simplificationOnFlats A)) =
      Fintype.card (GraphSpanningTrees (completeLabelledGraph P.parts)) :=
  Fintype.card_congr (partitionContractionBasesEquivTrees P)

theorem partitionRankTight_count_complete_bases (k : ℕ) :
    Fintype.card (PartitionRankTightAntichain α k) =
      ∑ Q : {Q : Finpartition (Finset.univ : Finset α) // Q.parts.card = k + 1},
        Fintype.card (MatroidBases (cycleMatroid (completeLabelledGraph Q.1.parts))) := by
  rw [partitionRankTight_count_by_blocks]
  apply Finset.sum_congr rfl
  intro Q _hQ
  exact partitionSimplificationBases_count Q.1

/-- The manuscript sum now has literal complete-graph spanning-tree
coefficients. The numerical Cayley and Stirling evaluations are not assumed. -/
theorem partitionRankTight_count_complete_trees (k : ℕ) :
    Fintype.card (PartitionRankTightAntichain α k) =
      ∑ Q : {Q : Finpartition (Finset.univ : Finset α) // Q.parts.card = k + 1},
        Fintype.card (GraphSpanningTrees (completeLabelledGraph Q.1.parts)) := by
  rw [partitionRankTight_count_by_blocks]
  apply Finset.sum_congr rfl
  intro Q _hQ
  exact partition_contraction_simplification_tree_count Q.1

end BooleanAntichainsKernel
