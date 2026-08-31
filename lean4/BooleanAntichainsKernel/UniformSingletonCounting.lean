import BooleanAntichainsKernel.SingletonAntichains
import BooleanAntichainsKernel.UniformFlats
import Mathlib.Data.Finset.Powerset

namespace BooleanAntichainsKernel

open Set Finset
open scoped Classical

variable {α : Type*} [Fintype α]

abbrev SmallGroundSubsets (E : Set α) (r : ℕ) :=
  {S : Finset α // S ⊆ E.toFinset ∧ S.card < r}

noncomputable instance (E : Set α) (r : ℕ) : Fintype (SmallGroundSubsets E r) := Subtype.fintype _

noncomputable def uniformOnProperFlatEquivSmallSubsets (E : Set α) (r : ℕ) (hr : r ≤ E.ncard) :
    {F : MatroidFlat (uniformOn E r) // F ≠ ⊤} ≃ SmallGroundSubsets E r where
  toFun F := ⟨F.1.1.toFinset, by
    have hne : F.1.1 ≠ E := fun h ↦ F.2 (Subtype.ext h)
    have h := (uniformOn_properFlat_iff E r hr F.1.1).mp ⟨F.1.2, hne⟩
    refine ⟨fun e he ↦ Set.mem_toFinset.mpr (h.1 (Set.mem_toFinset.mp he)), ?_⟩
    simpa only [Set.ncard_eq_toFinset_card'] using h.2⟩
  invFun S := by
    have h := (uniformOn_properFlat_iff E r hr (S.1 : Set α)).mpr
      ⟨fun e he ↦ Set.mem_toFinset.mp (S.2.1 he),
        by simpa only [Set.ncard_coe_finset] using S.2.2⟩
    exact ⟨⟨S.1, h.1⟩, fun htop ↦ h.2 (congrArg Subtype.val htop)⟩
  left_inv F := by
    apply Subtype.ext
    apply Subtype.ext
    exact Set.coe_toFinset F.1.1
  right_inv S := by
    apply Subtype.ext
    ext e
    simp

/-- Split the very same small subsets by their cardinality, without
substituting a numeric formula for their carrier. -/
noncomputable def smallGroundSubsetsEquivSigma (E : Set α) (r : ℕ) :
    SmallGroundSubsets E r ≃ Σ b : Fin r, ↥(E.toFinset.powersetCard b.1) where
  toFun S := ⟨⟨S.1.card, S.2.2⟩, ⟨S.1, Finset.mem_powersetCard.mpr ⟨S.2.1, rfl⟩⟩⟩
  invFun B := ⟨B.2.1, (Finset.mem_powersetCard.mp B.2.2).1,
    (Finset.mem_powersetCard.mp B.2.2).2.trans_lt B.1.2⟩
  left_inv _ := rfl
  right_inv B := by
    rcases B with ⟨⟨b, hb⟩, ⟨S, hS⟩⟩
    have hc : S.card = b := (Finset.mem_powersetCard.mp hS).2
    subst b
    rfl

theorem smallGroundSubsets_count (E : Set α) (r : ℕ) :
    Fintype.card (SmallGroundSubsets E r) = ∑ b ∈ Finset.range r, E.ncard.choose b := by
  calc
    _ = Fintype.card (Σ b : Fin r, ↥(E.toFinset.powersetCard b.1)) :=
      Fintype.card_congr (smallGroundSubsetsEquivSigma E r)
    _ = ∑ b : Fin r, E.ncard.choose b.1 := by
      simp only [Fintype.card_sigma, Fintype.card_coe, Finset.card_powersetCard,
        ← Set.ncard_eq_toFinset_card']
    _ = _ := Fin.sum_univ_eq_sum_range (fun b ↦ E.ncard.choose b) r

theorem uniformOn_singleton_count (E : Set α) (r : ℕ) (hr : r ≤ E.ncard) :
    Fintype.card (BooleanAntichain 1 (MatroidFlat (uniformOn E r))) =
      ∑ b ∈ Finset.range r, E.ncard.choose b := by
  rw [singletonAntichain_count,
    Fintype.card_congr (uniformOnProperFlatEquivSmallSubsets E r hr), smallGroundSubsets_count]

theorem uniform_singleton_count (n r : ℕ) (hr : r ≤ n) :
    Fintype.card (BooleanAntichain 1 (MatroidFlat (uniformOn (Set.univ : Set (Fin n)) r))) =
      ∑ b ∈ Finset.range r, n.choose b := by
  have hrE : r ≤ (Set.univ : Set (Fin n)).ncard := by
    simpa only [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] using hr
  simpa only [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] using
    uniformOn_singleton_count (Set.univ : Set (Fin n)) r hrE

end BooleanAntichainsKernel
