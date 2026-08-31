import BooleanAntichainsKernel.UniformFlats
import BooleanAntichainsKernel.RankTightEnumeration
import BooleanAntichainsKernel.HeightGapEndpoints
import Mathlib.Data.Finset.Powerset

namespace BooleanAntichainsKernel

open Set Finset
open scoped Classical

variable {α : Type*} [Fintype α]

theorem uniformOn_hasCorank_iff (E : Set α) (r : ℕ) (hr : r ≤ E.ncard)
    (k : ℕ) (hk : 0 < k) (X : MatroidFlat (uniformOn E r)) :
    HasCorank (uniformOn E r) k X ↔ X.1.ncard + k = r := by
  have htop : MatroidFlat.rank (⊤ : MatroidFlat (uniformOn E r)) = r :=
    uniformOn_ground_rank E r hr
  constructor
  · intro hcorank
    have hsum := (hasCorank_iff_add k X).mp hcorank
    rw [htop] at hsum
    have hne : X.1 ≠ E := by
      intro hXE
      have hxr : MatroidFlat.rank X = r := by
        change matroidRank (uniformOn E r) X.1 = r
        rw [hXE, uniformOn_ground_rank E r hr]
      rw [hxr] at hsum
      omega
    have hsmall := ((uniformOn_properFlat_iff E r hr X.1).mp ⟨X.2, hne⟩).2
    have hxrank : MatroidFlat.rank X = X.1.ncard :=
      matroidRank_indep ((uniformOn_indep_iff E r X.1).mpr ⟨X.2.subset_ground, hsmall.le⟩)
    rwa [hxrank] at hsum
  · intro hsum
    apply (hasCorank_iff_add k X).mpr
    have hxrank : MatroidFlat.rank X = X.1.ncard :=
      matroidRank_indep ((uniformOn_indep_iff E r X.1).mpr
        ⟨X.2.subset_ground, by omega⟩)
    rw [hxrank, htop]
    exact hsum

/-- Positive-corank flats are exactly the actual (r-k)-subsets of E. -/
noncomputable def uniformOnCorankEquivPowersetCard (E : Set α) (r : ℕ) (hr : r ≤ E.ncard)
    (k : ℕ) (hk : 0 < k) (hkr : k ≤ r) :
    CorankFlat (uniformOn E r) k ≃ ↥(E.toFinset.powersetCard (r - k)) where
  toFun X := ⟨X.1.1.toFinset, by
    apply Finset.mem_powersetCard.mpr
    refine ⟨fun e he ↦ Set.mem_toFinset.mpr
      (X.1.2.subset_ground (Set.mem_toFinset.mp he)), ?_⟩
    have hc := (uniformOn_hasCorank_iff E r hr k hk X.1).mp X.2
    rw [← Set.ncard_eq_toFinset_card']
    omega⟩
  invFun B := by
    have hB := Finset.mem_powersetCard.mp B.2
    have hBE : (B.1 : Set α) ⊆ E := fun e he ↦ Set.mem_toFinset.mp (hB.1 he)
    have hcard : (B.1 : Set α).ncard = r - k := by
      simpa only [Set.ncard_coe_finset] using hB.2
    let X : MatroidFlat (uniformOn E r) := ⟨B.1,
      (uniformOn_isFlat_iff E r (B.1 : Set α)).mpr ⟨hBE, Or.inl (by rw [hcard]; omega)⟩⟩
    refine ⟨X, (uniformOn_hasCorank_iff E r hr k hk X).mpr ?_⟩
    change (B.1 : Set α).ncard + k = r
    rw [hcard]
    omega
  left_inv X := by
    apply Subtype.ext
    apply Subtype.ext
    exact Set.coe_toFinset X.1.1
  right_inv B := by
    apply Subtype.ext
    ext e
    simp

theorem uniformOn_corankFlat_count (E : Set α) (r : ℕ) (hr : r ≤ E.ncard)
    (k : ℕ) (hk : 0 < k) (hkr : k ≤ r) :
    Fintype.card (CorankFlat (uniformOn E r) k) = E.ncard.choose (r - k) := by
  rw [Fintype.card_congr (uniformOnCorankEquivPowersetCard E r hr k hk hkr),
    Fintype.card_coe, Finset.card_powersetCard, ← Set.ncard_eq_toFinset_card']

noncomputable def rankTightZeroEquiv (M : Matroid α) :
    RankTightAntichain M 0 ≃ BooleanAntichain 0 (MatroidFlat M) where
  toFun C := C.1
  invFun C := ⟨C, by
    have hC : C.1 = ∅ := Finset.card_eq_zero.mp C.2.1
    simp [IsRankTight, hC]⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem rankTight_count_zero (M : Matroid α) :
    Fintype.card (RankTightAntichain M 0) = 1 := by
  rw [Fintype.card_congr (rankTightZeroEquiv M), booleanAntichain_count_zero]

end BooleanAntichainsKernel
