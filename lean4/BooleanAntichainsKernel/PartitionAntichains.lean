import BooleanAntichainsKernel.PartitionFlatRank
import BooleanAntichainsKernel.RankTightEnumeration

namespace BooleanAntichainsKernel

open scoped Classical Matroid

variable {α : Type*} [Fintype α] [DecidableEq α]

local notation "M" => cycleMatroid (completeLabelledGraph α)

def partitionRank (P : Finpartition (Finset.univ : Finset α)) : ℕ := Fintype.card α - P.parts.card

/-- Literal rank-tightness on the finite-block partition carrier, using
ordinary integer subtraction to keep all out-of-range layers empty. -/
def IsPartitionRankTight {k : ℕ}
    (C : BooleanAntichain k (Finpartition (Finset.univ : Finset α))) : Prop :=
  (partitionRank (C.1.inf id) : ℤ) = (partitionRank (⊤ : Finpartition (Finset.univ : Finset α)) : ℤ) - (k : ℤ)

noncomputable def partitionAntichainEquiv (k : ℕ) :
    BooleanAntichain k (Finpartition (Finset.univ : Finset α)) ≃ BooleanAntichain k (MatroidFlat M) :=
  booleanAntichainOrderIsoEquiv finitePartitionCompleteFlatOrderIso k

theorem partitionAntichainEquiv_val (k : ℕ)
    (C : BooleanAntichain k (Finpartition (Finset.univ : Finset α))) :
    (partitionAntichainEquiv k C).1 = mapFamily finitePartitionCompleteFlatOrderIso C.1 := rfl

theorem partitionAntichainEquiv_meet (k : ℕ)
    (C : BooleanAntichain k (Finpartition (Finset.univ : Finset α))) :
    (partitionAntichainEquiv k C).1.inf id = finitePartitionCompleteFlatOrderIso (C.1.inf id) := by
  rw [partitionAntichainEquiv_val, mapFamily, Equiv.finsetCongr_apply, Finset.inf_map]
  exact (map_finset_inf finitePartitionCompleteFlatOrderIso C.1 id).symm

theorem partitionAntichain_rankTight_iff {k : ℕ}
    (C : BooleanAntichain k (Finpartition (Finset.univ : Finset α))) :
    IsRankTight (partitionAntichainEquiv k C) ↔ IsPartitionRankTight C := by
  rw [← hasCorank_bottom_iff_rankTight]
  change (MatroidFlat.rank ((partitionAntichainEquiv k C).1.inf id) : ℤ) =
    (MatroidFlat.rank (⊤ : MatroidFlat M) : ℤ) - (k : ℤ) ↔ _
  rw [partitionAntichainEquiv_meet, partitionFlat_rank]
  have ht : MatroidFlat.rank (⊤ : MatroidFlat M) =
      partitionRank (⊤ : Finpartition (Finset.univ : Finset α)) := by
    have h := partitionFlat_rank (⊤ : Finpartition (Finset.univ : Finset α))
    rw [map_top] at h
    exact h
  rw [ht]
  rfl

abbrev PartitionRankTightAntichain (α : Type*) [Fintype α] [DecidableEq α] (k : ℕ) :=
  {C : BooleanAntichain k (Finpartition (Finset.univ : Finset α)) // IsPartitionRankTight C}

noncomputable instance {k : ℕ} : Fintype (PartitionRankTightAntichain α k) := Subtype.fintype _

noncomputable def partitionRankTightEquivMatroid (k : ℕ) :
    PartitionRankTightAntichain α k ≃ RankTightAntichain M k :=
  Equiv.subtypeEquiv (partitionAntichainEquiv k) (fun C ↦ (partitionAntichain_rankTight_iff C).symm)

theorem partitionRankTight_count_eq_matroid (k : ℕ) :
    Fintype.card (PartitionRankTightAntichain α k) = Fintype.card (RankTightAntichain M k) :=
  Fintype.card_congr (partitionRankTightEquivMatroid k)

variable [Nonempty α]

theorem partitionRankTight_block_iff {k : ℕ}
    (C : BooleanAntichain k (Finpartition (Finset.univ : Finset α))) :
    IsPartitionRankTight C ↔ (C.1.inf id).parts.card = k + 1 := by
  rw [← partitionAntichain_rankTight_iff, ← hasCorank_bottom_iff_rankTight,
    partitionAntichainEquiv_meet, partitionFlat_hasCorank_iff]

noncomputable def partitionCorankEquiv (k : ℕ) :
    {P : Finpartition (Finset.univ : Finset α) // P.parts.card = k + 1} ≃ CorankFlat M k :=
  Equiv.subtypeEquiv finitePartitionCompleteFlatOrderIso.toEquiv
    (fun P ↦ (partitionFlat_hasCorank_iff k P).symm)

/-- Consume the proved rank-tight theorem with the literal (k+1)-block
index. The coefficients remain actual contraction-simplification bases;
their complete-graph/Cayley evaluation is a separate obligation. -/
theorem partitionRankTight_count_by_blocks (k : ℕ) :
    Fintype.card (PartitionRankTightAntichain α k) =
      ∑ P : {P : Finpartition (Finset.univ : Finset α) // P.parts.card = k + 1},
        Fintype.card (MatroidBases (simplificationOnFlats (M ／ (finitePartitionCompleteFlatOrderIso P.1).1))) := by
  calc
    _ = Fintype.card (RankTightAntichain M k) := partitionRankTight_count_eq_matroid k
    _ = ∑ X : CorankFlat M k, Fintype.card (SimplifiedBasis (M ／ X.1.1)) :=
      rankTight_count_by_bottom_subtype M k
    _ = ∑ X : CorankFlat M k, Fintype.card (MatroidBases (simplificationOnFlats (M ／ X.1.1))) := by
      apply Finset.sum_congr rfl
      intro X _hX
      exact simplifiedBasis_count_eq_actualMatroidBases
    _ = _ := (partitionCorankEquiv k).sum_comp
      (fun X : CorankFlat M k ↦ Fintype.card (MatroidBases (simplificationOnFlats (M ／ X.1.1)))) |>.symm

end BooleanAntichainsKernel
