import BooleanAntichainsKernel.FreeMatroid
import BooleanAntichainsKernel.RankTightEnumeration
import Mathlib.Data.Finset.Powerset

namespace BooleanAntichainsKernel

open Set Finset
open scoped Classical Matroid

variable {α : Type*} [Fintype α]

lemma freeOnUniv_hasCorank_iff (k : ℕ)
    (X : MatroidFlat (Matroid.freeOn (Set.univ : Set α))) :
    HasCorank (Matroid.freeOn (Set.univ : Set α)) k X ↔
      X.1.toFinset.card + k = Fintype.card α := by
  rw [hasCorank_iff_add, freeOn_flat_rank, freeOn_top_rank, Set.ncard_univ,
    Nat.card_eq_fintype_card, Set.ncard_eq_toFinset_card']

/-- The paper's complement correspondence for every corank, including the
empty layer above the rank. No truncated corank is used. -/
noncomputable def freeOnCorankFlatEquivPowersetCard (k : ℕ) :
    CorankFlat (Matroid.freeOn (Set.univ : Set α)) k ≃
      ↥((Finset.univ : Finset α).powersetCard k) where
  toFun X := ⟨Finset.univ \ X.1.1.toFinset, by
    apply Finset.mem_powersetCard.mpr
    refine ⟨Finset.subset_univ _, ?_⟩
    have hc := (freeOnUniv_hasCorank_iff k X.1).mp X.2
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]
    omega⟩
  invFun S := ⟨⟨(Finset.univ \ S.1 : Finset α),
      (freeOn_isFlat_iff _ _).mpr (Set.subset_univ _)⟩, by
    rw [freeOnUniv_hasCorank_iff]
    simp only [Finset.toFinset_coe]
    have hcard := (Finset.mem_powersetCard.mp S.2).2
    have hle : S.1.card ≤ Fintype.card α := by
      simpa using Finset.card_le_card (Finset.subset_univ S.1)
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, hcard]
    omega⟩
  left_inv X := by
    apply Subtype.ext
    apply Subtype.ext
    change ((Finset.univ \ (Finset.univ \ X.1.1.toFinset) : Finset α) : Set α) = X.1.1
    rw [Finset.sdiff_sdiff_eq_self (Finset.subset_univ _), Set.coe_toFinset]
  right_inv S := by
    apply Subtype.ext
    ext i
    simp

theorem freeOn_corankFlat_count (k : ℕ) :
    Fintype.card (CorankFlat (Matroid.freeOn (Set.univ : Set α)) k) =
      (Fintype.card α).choose k := by
  rw [Fintype.card_congr (freeOnCorankFlatEquivPowersetCard k), Fintype.card_coe,
    Finset.card_powersetCard, Finset.card_univ]

/-- Corollary rank-tight specialized through the actual free contractions,
whose simplification bases were proved unique. -/
theorem freeOn_rankTight_count (k : ℕ) :
    Fintype.card (RankTightAntichain (Matroid.freeOn (Set.univ : Set α)) k) =
      (Fintype.card α).choose k := by
  rw [rankTight_count_by_bottom_subtype]
  calc
    _ = ∑ _X : CorankFlat (Matroid.freeOn (Set.univ : Set α)) k, 1 := by
      apply Finset.sum_congr rfl
      intro X _
      exact freeOn_contraction_simplifiedBasis_count Set.univ X.1.1 (Set.subset_univ _)
    _ = Fintype.card (CorankFlat (Matroid.freeOn (Set.univ : Set α)) k) := by simp
    _ = (Fintype.card α).choose k := freeOn_corankFlat_count k

end BooleanAntichainsKernel
