import BooleanAntichainsKernel.PartitionContractionFlats
import BooleanAntichainsKernel.SimplificationFlatTransport
import BooleanAntichainsKernel.CompleteGraphRankOne

namespace BooleanAntichainsKernel

open scoped Classical Matroid

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (P : Finpartition (Finset.univ : Finset α))

local notation "A" => Matroid.contract (cycleMatroid (completeLabelledGraph α))
  (Subtype.val (finitePartitionCompleteFlatOrderIso P))
local notation "B" => cycleMatroid (completeLabelledGraph (Finpartition.parts P))

/-- The simplification ground is identified with actual unordered pairs
of distinct original blocks. -/
noncomputable def partitionSimplificationEdgeEquiv :
    RankOneFlat A ≃ (completeLabelledGraph P.parts).edgeSet :=
  (rankOneFlatEquivOfOrderIso (partitionContractionFlatOrderIso P)
    (partitionContractionFlatOrderIso_rank P)).trans completeRankOneRepresentativeEquiv

noncomputable def partitionSimplificationLabel (F : RankOneFlat A) : Sym2 P.parts :=
  (partitionSimplificationEdgeEquiv P F).1

theorem partitionSimplificationEdgeEquiv_val (F : RankOneFlat A) :
    (partitionSimplificationEdgeEquiv P F).1 =
      flatIsoRepresentativeMap (partitionContractionFlatOrderIso P) (partitionContractionFlatOrderIso_rank P) F := rfl

theorem partitionSimplificationLabel_injective : Function.Injective (partitionSimplificationLabel P) :=
  Subtype.val_injective.comp (partitionSimplificationEdgeEquiv P).injective

theorem partitionSimplificationLabel_range :
    Set.range (partitionSimplificationLabel P) = (B).E := by
  ext q
  constructor
  · rintro ⟨F, rfl⟩
    exact (partitionSimplificationEdgeEquiv P F).2
  · intro hq
    obtain ⟨F, hF⟩ := (partitionSimplificationEdgeEquiv P).surjective ⟨q, hq⟩
    exact ⟨F, congrArg (fun e : (completeLabelledGraph P.parts).edgeSet ↦ e.1) hF⟩

theorem partitionSimplificationLabel_preimage_ground :
    partitionSimplificationLabel P ⁻¹' (B).E = Set.univ := by
  ext F
  exact iff_of_true (partitionSimplificationEdgeEquiv P F).2 (Set.mem_univ F)

/-- Equality of actual matroids after the proved ground equivalence:
every independent set is transported by the existing simplification proof. -/
theorem partition_simplification_eq_comap :
    simplificationOnFlats A = (B).comap (partitionSimplificationLabel P) :=
  simplificationFlatIso_eq_comap (partitionContractionFlatOrderIso P) (partitionContractionFlatOrderIso_rank P)

theorem partitionContraction_loops_empty : (A).loops = ∅ := by
  change (A).closure ∅ = ∅
  rw [Matroid.contract_closure_eq, Set.empty_union, (finitePartitionCompleteFlatOrderIso P).2.closure,
    Set.sdiff_self]

/-- Each contracted nonloop parallel class is the full original-edge
fibre of one block pair. All parallel multiplicities are retained. -/
theorem partition_simplification_class (F : RankOneFlat A) :
    F.1.1 \ (A).loops = {q : Sym2 α | partitionBlockEdgeMap P q = partitionSimplificationLabel P F} := by
  have hsingle : (partitionContractionFlatOrderIso P F.1).1 = {partitionSimplificationLabel P F} :=
    completeRankOneFlat_singleton
      (rankOneFlatEquivOfOrderIso (partitionContractionFlatOrderIso P) (partitionContractionFlatOrderIso_rank P) F)
  rw [partitionContraction_loops_empty, Set.sdiff_empty]
  calc
    F.1.1 = partitionBlockEdgeMap P ⁻¹' (partitionContractionFlatOrderIso P F.1).1 :=
      (partitionContractionFlatOrderIso_preimage P F.1).symm
    _ = partitionBlockEdgeMap P ⁻¹' {partitionSimplificationLabel P F} :=
      congrArg (fun S : Set (Sym2 P.parts) ↦ partitionBlockEdgeMap P ⁻¹' S) hsingle
    _ = _ := rfl

theorem partition_simplification_class_nonempty (t : (completeLabelledGraph P.parts).edgeSet) :
    (((partitionSimplificationEdgeEquiv P).symm t).1.1 \ (A).loops).Nonempty := by
  rw [partition_simplification_class]
  obtain ⟨q, hq⟩ := partitionBlockEdgeMap_surjective P t.1
  have ht : partitionSimplificationLabel P ((partitionSimplificationEdgeEquiv P).symm t) = t.1 :=
    congrArg (fun e : (completeLabelledGraph P.parts).edgeSet ↦ e.1)
      ((partitionSimplificationEdgeEquiv P).apply_symm_apply t)
  exact ⟨q, hq.trans ht.symm⟩

end BooleanAntichainsKernel
