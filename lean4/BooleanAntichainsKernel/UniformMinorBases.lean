import BooleanAntichainsKernel.UniformMatroid
import BooleanAntichainsKernel.TuttePolynomial
import Mathlib.Data.Finset.Powerset

namespace BooleanAntichainsKernel

open Set Finset
open scoped Classical Matroid

variable {α : Type*} [Fintype α]

/-- Equality of the actual contracted matroid, established from independence
on the exact remaining ground set. The rank subtraction uses X.ncard ≤ r. -/
theorem uniformOn_contract (E : Set α) (r : ℕ) (X : Set α)
    (hXE : X ⊆ E) (hcard : X.ncard ≤ r) :
    (uniformOn E r) ／ X = uniformOn (E \ X) (r - X.ncard) := by
  refine Matroid.ext_indep ?_ ?_
  · rfl
  intro I hI
  change I ⊆ E \ X at hI
  have hdis : Disjoint I X := (Set.subset_sdiff.mp hI).2
  have hIE : I ⊆ E := (Set.subset_sdiff.mp hI).1
  have hunion : I ∪ X ⊆ E := Set.union_subset hIE hXE
  have hXind : (uniformOn E r).Indep X := (uniformOn_indep_iff E r X).mpr ⟨hXE, hcard⟩
  rw [hXind.contract_indep_iff, uniformOn_indep_iff, uniformOn_indep_iff]
  simp only [hdis, hunion, hI, true_and, Set.ncard_union_eq hdis]
  omega

/-- Bases are mapped to their very same r-subsets of the actual ground set. -/
noncomputable def uniformOnBasesEquivPowersetCard (E : Set α) (r : ℕ) (hr : r ≤ E.ncard) :
    MatroidBases (uniformOn E r) ≃ ↥(E.toFinset.powersetCard r) where
  toFun B := ⟨B.1, by
    have h := (uniformOn_isBase_iff E r hr (B.1 : Set α)).mp B.2
    apply Finset.mem_powersetCard.mpr
    refine ⟨fun e he ↦ Set.mem_toFinset.mpr (h.1 he), ?_⟩
    simpa only [Set.ncard_coe_finset] using h.2⟩
  invFun B := ⟨B.1, by
    have h := Finset.mem_powersetCard.mp B.2
    apply (uniformOn_isBase_iff E r hr (B.1 : Set α)).mpr
    refine ⟨fun e he ↦ Set.mem_toFinset.mp (h.1 he), ?_⟩
    simpa only [Set.ncard_coe_finset] using h.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem uniformOn_basis_count (E : Set α) (r : ℕ) (hr : r ≤ E.ncard) :
    Fintype.card (MatroidBases (uniformOn E r)) = E.ncard.choose r := by
  rw [Fintype.card_congr (uniformOnBasesEquivPowersetCard E r hr), Fintype.card_coe,
    Finset.card_powersetCard, ← Set.ncard_eq_toFinset_card']

theorem uniformOn_contraction_basis_count (E : Set α) (r : ℕ) (hr : r ≤ E.ncard)
    (X : Set α) (hXE : X ⊆ E) (hcard : X.ncard ≤ r) :
    Fintype.card (MatroidBases ((uniformOn E r) ／ X)) =
      (E.ncard - X.ncard).choose (r - X.ncard) := by
  have hrnew : r - X.ncard ≤ (E \ X).ncard := by
    rw [Set.ncard_sdiff hXE]
    omega
  rw [uniformOn_contract E r X hXE hcard, uniformOn_basis_count _ _ hrnew, Set.ncard_sdiff hXE]

end BooleanAntichainsKernel
