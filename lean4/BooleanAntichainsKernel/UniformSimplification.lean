import BooleanAntichainsKernel.UniformFlats
import BooleanAntichainsKernel.UniformMinorBases
import BooleanAntichainsKernel.SimplifiedBasisCounts

namespace BooleanAntichainsKernel

open Set Finset
open scoped Classical

variable {α : Type*} [Fintype α]

/-- The actual nonloop parallel class of each rank-one flat is a singleton
in a uniform matroid of rank at least two. -/
theorem uniformOn_parallelClass_card_one (E : Set α) (r : ℕ) (hr : 2 ≤ r)
    (F : MatroidFlat (uniformOn E r)) (hF : MatroidFlat.rank F = 1) :
    (parallelClassElements F).card = 1 := by
  have hmin : min r F.1.ncard = 1 :=
    (uniformOn_rank E r F.1 F.2.subset_ground).symm.trans hF
  have hc : F.1.ncard = 1 := by omega
  have hbot : (uniformOn E r).closure ∅ = ∅ :=
    uniformOn_closure_of_card_lt E r ∅ (Set.empty_subset E)
      (by simpa using (show 0 < r by omega))
  unfold parallelClassElements
  rw [← Set.ncard_eq_toFinset_card', hbot, Set.sdiff_empty]
  exact hc

theorem uniformOn_rank_one_simplifiedBasis_count (E : Set α) (hE : 1 ≤ E.ncard) :
    Fintype.card (SimplifiedBasis (uniformOn E 1)) = 1 :=
  simplifiedBasis_count_rank_one (uniformOn E 1) (uniformOn_ground_rank E 1 hE)

/-- The basis count survives the genuine simplification, by singleton class
choices, rather than by defining a simplified count to be the original count. -/
theorem uniformOn_simplifiedBasis_count (E : Set α) (r : ℕ)
    (hr : 2 ≤ r) (hrE : r ≤ E.ncard) :
    Fintype.card (SimplifiedBasis (uniformOn E r)) = E.ncard.choose r := by
  rw [simplifiedBasis_count_of_singleton_classes (uniformOn E r)
    (uniformOn_parallelClass_card_one E r hr), uniformOn_basis_count E r hrE]

end BooleanAntichainsKernel
