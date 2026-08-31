import BooleanAntichainsKernel.MatroidRank
import Mathlib.Combinatorics.Matroid.Minor.Contract

/-! The contraction rank identity used in the interval proof, derived from
actual bases of the contracted set and the contraction. -/

namespace BooleanAntichainsKernel

open Set
open scoped Matroid

variable {α : Type*} [Fintype α] {M : Matroid α}

lemma matroidRank_isBasis {I X : Set α} (hI : M.IsBasis I X) :
    matroidRank M X = I.ncard := by
  apply ENat.coe_inj.mp
  rw [coe_matroidRank, hI.eRk_eq_encard, Set.coe_ncard_eq_encard]

omit [Fintype α] in
lemma matroidRank_restrict (M : Matroid α) {X Y : Set α} (hXY : X ⊆ Y) :
    matroidRank (M ↾ Y) X = matroidRank M X := by
  unfold matroidRank
  rw [M.restrict_eRk_eq hXY]

theorem matroidRank_contract_add (M : Matroid α) {C S : Set α}
    (hC : C ⊆ M.E) (hS : S ⊆ M.E \ C) :
    matroidRank (M ／ C) S + matroidRank M C = matroidRank M (S ∪ C) := by
  obtain ⟨I, hI⟩ := M.exists_isBasis C hC
  obtain ⟨J, hJ⟩ := (M ／ C).exists_isBasis S hS
  obtain ⟨hind, hCJ⟩ := hI.contract_indep_iff.mp hJ.indep
  have hJI : Disjoint J I := (hCJ.mono_left hI.subset).symm
  have hcl : M.closure (J ∪ I) = M.closure (J ∪ C) :=
    M.closure_union_congr_right hI.closure_eq_closure
  have hScl : S ⊆ M.closure (J ∪ I) := by
    intro e heS
    have he := hJ.subset_closure heS
    rw [Matroid.contract_closure_eq] at he
    rw [hcl]
    exact he.1
  have hCcl : C ⊆ M.closure (J ∪ I) :=
    hI.subset_closure.trans (M.closure_subset_closure Set.subset_union_right)
  have hUnion : M.IsBasis (J ∪ I) (S ∪ C) :=
    hind.isBasis_of_subset_of_subset_closure (Set.union_subset_union hJ.subset hI.subset)
      (Set.union_subset hScl hCcl)
  rw [matroidRank_isBasis hJ, matroidRank_isBasis hI, matroidRank_isBasis hUnion,
    Set.ncard_union_eq hJI]

/-- The displayed contraction rank formula, on the actual minor ground. -/
theorem matroidRank_contract (M : Matroid α) {C S : Set α}
    (hC : C ⊆ M.E) (hS : S ⊆ M.E \ C) :
    matroidRank (M ／ C) S = matroidRank M (S ∪ C) - matroidRank M C := by
  have h := matroidRank_contract_add M hC hS
  omega

end BooleanAntichainsKernel
