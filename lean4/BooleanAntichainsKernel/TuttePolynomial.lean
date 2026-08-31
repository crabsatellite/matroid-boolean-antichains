import BooleanAntichainsKernel.MatroidRank
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Powerset

/-! The standard rank-subset expansion of the Tutte polynomial and its
basis evaluation. The polynomial is constructed, not supplied by a reference
gate or defined to be the number of bases. -/

namespace BooleanAntichainsKernel

open Set Finset
open scoped Classical

variable {α : Type*} [Fintype α]

abbrev MatroidBases (M : Matroid α) := {B : Finset α // M.IsBase (B : Set α)}

noncomputable instance {M : Matroid α} : Fintype (MatroidBases M) := by
  classical
  exact Subtype.fintype _

lemma matroidRank_finset_le_card (M : Matroid α) (B : Finset α) :
    matroidRank M (B : Set α) ≤ B.card := by
  apply ENat.coe_le_coe.mp
  rw [coe_matroidRank]
  simpa using M.eRk_le_encard (B : Set α)

lemma matroid_isBase_iff_rank (M : Matroid α) (B : Finset α) :
    M.IsBase (B : Set α) ↔ (B : Set α) ⊆ M.E ∧
      matroidRank M (B : Set α) = B.card ∧
      matroidRank M (B : Set α) = matroidRank M M.E := by
  constructor
  · intro hB
    refine ⟨hB.subset_ground, ?_, ?_⟩
    · simpa using matroidRank_indep hB.indep
    · rw [← matroidRank_closure M (B : Set α), hB.closure_eq]
  · rintro ⟨hBE, hcard, hrank⟩
    have hind : M.Indep (B : Set α) := by
      apply (Matroid.indep_iff_eRk_eq_encard_of_finite (Finset.finite_toSet B)).mpr
      rw [← coe_matroidRank, hcard]
      simp
    have hr : M.eRk M.E ≤ M.eRk (B : Set α) := by
      rw [← coe_matroidRank, ← coe_matroidRank, hrank]
    have hc := (M.isRkFinite_of_finite (Finset.finite_toSet B)).closure_eq_closure_of_subset_of_eRk_ge_eRk hBE hr
    rw [M.closure_ground] at hc
    exact hind.isBase_of_ground_subset_closure hc.symm.subset

/-- `x` is variable 0 and `y` is variable 1. -/
noncomputable def matroidTuttePolynomial (M : Matroid α) : MvPolynomial (Fin 2) ℤ := by
  classical
  exact ∑ B ∈ M.E.toFinset.powerset,
    (MvPolynomial.X 0 - 1) ^ (matroidRank M M.E - matroidRank M (B : Set α)) *
    (MvPolynomial.X 1 - 1) ^ (B.card - matroidRank M (B : Set α))

lemma tutte_subset_term_at_one (M : Matroid α) (B : Finset α) (hBE : (B : Set α) ⊆ M.E) :
    MvPolynomial.eval (fun _ : Fin 2 ↦ (1 : ℤ))
      ((MvPolynomial.X 0 - 1) ^ (matroidRank M M.E - matroidRank M (B : Set α)) *
       (MvPolynomial.X 1 - 1) ^ (B.card - matroidRank M (B : Set α))) =
      (if M.IsBase (B : Set α) then (1 : ℤ) else 0) := by
  classical
  simp only [map_mul, map_pow, map_sub, MvPolynomial.eval_X, map_one, sub_self]
  have hrg := matroidRank_mono M hBE
  have hrc := matroidRank_finset_le_card M B
  by_cases hB : M.IsBase (B : Set α)
  · obtain ⟨_, hcard, hrank⟩ := (matroid_isBase_iff_rank M B).mp hB
    have hx : matroidRank M M.E - matroidRank M (B : Set α) = 0 := by omega
    have hy : B.card - matroidRank M (B : Set α) = 0 := by omega
    simp [hB, hx, hy]
  · have hn : ¬ (matroidRank M M.E - matroidRank M (B : Set α) = 0 ∧
        B.card - matroidRank M (B : Set α) = 0) := by
      rintro ⟨hx, hy⟩
      apply hB
      apply (matroid_isBase_iff_rank M B).mpr
      refine ⟨hBE, ?_, ?_⟩ <;> omega
    rcases not_and_or.mp hn with hx | hy
    · simp [hB, zero_pow hx]
    · simp [hB, zero_pow hy]

lemma sum_basis_indicators (M : Matroid α) :
    (∑ B ∈ M.E.toFinset.powerset, if M.IsBase (B : Set α) then (1 : ℤ) else 0) =
      Fintype.card (MatroidBases M) := by
  classical
  rw [Finset.sum_boole, Fintype.card_subtype]
  congr 1
  congr 1
  ext B
  simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_univ, true_and]
  constructor
  · exact And.right
  · intro hB
    refine ⟨?_, hB⟩
    intro x hx
    simpa using hB.subset_ground hx

/-- The kernel-derived standard identity `T_M(1,1) = b(M)`. -/
theorem matroidTutte_at_one_eq_number_of_bases (M : Matroid α) :
    MvPolynomial.eval (fun _ : Fin 2 ↦ (1 : ℤ)) (matroidTuttePolynomial M) =
      Fintype.card (MatroidBases M) := by
  classical
  rw [matroidTuttePolynomial, map_sum]
  calc
    _ = ∑ B ∈ M.E.toFinset.powerset, if M.IsBase (B : Set α) then (1 : ℤ) else 0 := by
      apply Finset.sum_congr rfl
      intro B hB
      apply tutte_subset_term_at_one M B
      intro x hx
      have hx' := (Finset.mem_powerset.mp hB) hx
      simpa using hx'
    _ = Fintype.card (MatroidBases M) := sum_basis_indicators M

end BooleanAntichainsKernel
