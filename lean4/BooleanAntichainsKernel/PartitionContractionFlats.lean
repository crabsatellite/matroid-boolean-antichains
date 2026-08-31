import BooleanAntichainsKernel.PartitionCoarseningBlocks
import BooleanAntichainsKernel.UpperFlatContraction

namespace BooleanAntichainsKernel

open scoped Classical Matroid

variable {α : Type*} [Fintype α] [DecidableEq α]

local notation "M" => cycleMatroid (completeLabelledGraph α)

noncomputable def partitionCoarseningContractOrderIso (P : Finpartition (Finset.univ : Finset α)) :
    Set.Ici P ≃o MatroidFlat (M ／ (finitePartitionCompleteFlatOrderIso P).1) :=
  (finitePartitionCompleteFlatOrderIso.Ici P).trans
    (upperFlatContractOrderIso (finitePartitionCompleteFlatOrderIso P))

theorem partitionCoarseningContractOrderIso_val (P : Finpartition (Finset.univ : Finset α))
    (Q : Set.Ici P) :
    (partitionCoarseningContractOrderIso P Q).1 =
      (finitePartitionCompleteFlatOrderIso Q.1).1 \ (finitePartitionCompleteFlatOrderIso P).1 := rfl

theorem partitionCoarseningContractOrderIso_rank (P : Finpartition (Finset.univ : Finset α))
    (Q : Set.Ici P) :
    MatroidFlat.rank (partitionCoarseningContractOrderIso P Q) = partitionRank Q.1 - partitionRank P := by
  change MatroidFlat.rank (upperFlatContractOrderIso (finitePartitionCompleteFlatOrderIso P)
    ((finitePartitionCompleteFlatOrderIso.Ici P) Q)) = _
  rw [upperFlatContractOrderIso_rank]
  change MatroidFlat.rank (finitePartitionCompleteFlatOrderIso Q.1) -
    MatroidFlat.rank (finitePartitionCompleteFlatOrderIso P) = _
  simp only [partitionFlat_rank, partitionRank]

/-- Actual contraction flats are identified with complete-graph flats on
the original blocks of P, not on a separately numbered surrogate carrier. -/
noncomputable def partitionContractionFlatOrderIso (P : Finpartition (Finset.univ : Finset α)) :
    MatroidFlat (M ／ (finitePartitionCompleteFlatOrderIso P).1) ≃o
      MatroidFlat (cycleMatroid (completeLabelledGraph P.parts)) :=
  (partitionCoarseningContractOrderIso P).symm.trans
    ((partitionCoarseningOrderIso P).trans finitePartitionCompleteFlatOrderIso)

theorem partitionContractionFlatOrderIso_on_coarsening (P : Finpartition (Finset.univ : Finset α))
    (Q : Set.Ici P) :
    partitionContractionFlatOrderIso P (partitionCoarseningContractOrderIso P Q) =
      finitePartitionCompleteFlatOrderIso (partitionCoarseningOrderIso P Q) := by
  change finitePartitionCompleteFlatOrderIso
    (partitionCoarseningOrderIso P ((partitionCoarseningContractOrderIso P).symm
      (partitionCoarseningContractOrderIso P Q))) = _
  rw [OrderIso.symm_apply_apply]

theorem partitionContractionFlatOrderIso_rank (P : Finpartition (Finset.univ : Finset α))
    (F : MatroidFlat (M ／ (finitePartitionCompleteFlatOrderIso P).1)) :
    MatroidFlat.rank (partitionContractionFlatOrderIso P F) = MatroidFlat.rank F := by
  obtain ⟨Q, rfl⟩ := (partitionCoarseningContractOrderIso P).surjective F
  rw [partitionContractionFlatOrderIso_on_coarsening, partitionFlat_rank,
    partitionCoarseningContractOrderIso_rank]
  exact Nat.eq_sub_of_add_eq (partitionCoarsening_rank_add P Q)

/-- The explicit collapse of original vertices to their original blocks,
applied to unordered original edge labels. -/
def partitionBlockEdgeMap (P : Finpartition (Finset.univ : Finset α)) : Sym2 α → Sym2 P.parts :=
  Sym2.map (finitePartitionBlockOf P)

theorem partitionBlockEdgeMap_pair (P : Finpartition (Finset.univ : Finset α)) (x y : α) :
    partitionBlockEdgeMap P s(x, y) = s(finitePartitionBlockOf P x, finitePartitionBlockOf P y) := rfl

theorem partitionBlockEdgeMap_surjective (P : Finpartition (Finset.univ : Finset α)) :
    Function.Surjective (partitionBlockEdgeMap P) := by
  intro q
  induction q using Sym2.inductionOn with
  | _ B C =>
    obtain ⟨x, rfl⟩ := finitePartitionBlockOf_surjective P B
    obtain ⟨y, rfl⟩ := finitePartitionBlockOf_surjective P C
    exact ⟨s(x, y), rfl⟩

theorem partitionCoarseningContractOrderIso_mem_pair (P : Finpartition (Finset.univ : Finset α))
    (Q : Set.Ici P) (x y : α) :
    s(x, y) ∈ (partitionCoarseningContractOrderIso P Q).1 ↔
      finitePartitionBlockOf P x ≠ finitePartitionBlockOf P y ∧ finitePartitionSetoid Q.1 x y := by
  rw [partitionCoarseningContractOrderIso_val]
  change ((x ≠ y ∧ finitePartitionSetoid Q.1 x y) ∧
    ¬(x ≠ y ∧ finitePartitionSetoid P x y)) ↔ _
  constructor
  · rintro ⟨⟨hxy, hrel⟩, hnot⟩
    exact ⟨fun hB ↦ hnot ⟨hxy, (finitePartitionBlockOf_eq_iff P x y).mp hB⟩, hrel⟩
  · rintro ⟨hB, hrel⟩
    have hxy : x ≠ y := fun h ↦ hB (congrArg (finitePartitionBlockOf P) h)
    exact ⟨⟨hxy, hrel⟩, fun hP ↦ hB ((finitePartitionBlockOf_eq_iff P x y).mpr hP.2)⟩

theorem partitionContractionFlatOrderIso_mem_pair (P : Finpartition (Finset.univ : Finset α))
    (F : MatroidFlat (M ／ (finitePartitionCompleteFlatOrderIso P).1)) (x y : α) :
    s(x, y) ∈ F.1 ↔ s(finitePartitionBlockOf P x, finitePartitionBlockOf P y) ∈
      (partitionContractionFlatOrderIso P F).1 := by
  obtain ⟨Q, rfl⟩ := (partitionCoarseningContractOrderIso P).surjective F
  rw [partitionContractionFlatOrderIso_on_coarsening, partitionCoarseningContractOrderIso_mem_pair]
  change _ ↔ s(finitePartitionBlockOf P x, finitePartitionBlockOf P y) ∈
    completeSetoidEdges (finitePartitionSetoid (partitionCoarseningOrderIso P Q))
  rw [completeSetoidEdges_mem_pair, partitionCoarseningOrderIso_rel]

/-- Every original edge is tested by its exact collapsed block pair. -/
theorem partitionContractionFlatOrderIso_mem (P : Finpartition (Finset.univ : Finset α))
    (F : MatroidFlat (M ／ (finitePartitionCompleteFlatOrderIso P).1)) (q : Sym2 α) :
    q ∈ F.1 ↔ partitionBlockEdgeMap P q ∈ (partitionContractionFlatOrderIso P F).1 := by
  induction q using Sym2.inductionOn with
  | _ x y => exact partitionContractionFlatOrderIso_mem_pair P F x y

theorem partitionContractionFlatOrderIso_preimage (P : Finpartition (Finset.univ : Finset α))
    (F : MatroidFlat (M ／ (finitePartitionCompleteFlatOrderIso P).1)) :
    partitionBlockEdgeMap P ⁻¹' (partitionContractionFlatOrderIso P F).1 = F.1 := by
  ext q
  exact (partitionContractionFlatOrderIso_mem P F q).symm

theorem partitionBlockEdgeMap_mem_ground (P : Finpartition (Finset.univ : Finset α)) (q : Sym2 α) :
    q ∈ (M ／ (finitePartitionCompleteFlatOrderIso P).1).E ↔
      partitionBlockEdgeMap P q ∈ (completeLabelledGraph P.parts).edgeSet := by
  have h := partitionContractionFlatOrderIso_mem P
    (⊤ : MatroidFlat (M ／ (finitePartitionCompleteFlatOrderIso P).1)) q
  rw [map_top] at h
  exact h

end BooleanAntichainsKernel
