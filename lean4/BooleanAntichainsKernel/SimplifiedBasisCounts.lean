import BooleanAntichainsKernel.BasisChoiceBijection

namespace BooleanAntichainsKernel

open Finset
open scoped Classical

variable {α : Type*} [Fintype α]

/-- In rank one the only simplified basis is the singleton top flat. -/
theorem simplifiedBasis_count_rank_one (M : Matroid α)
    (hr : MatroidFlat.rank (⊤ : MatroidFlat M) = 1) :
    Fintype.card (SimplifiedBasis M) = 1 := by
  let A0 : SimplifiedBasis M := ⟨{⊤}, by simp [IsSimplifiedBasis, hr]⟩
  apply Fintype.card_eq_one_iff.mpr
  refine ⟨A0, ?_⟩
  intro A
  have hcard : A.1.card = 1 := A.2.2.1.trans hr
  obtain ⟨F, hF⟩ := Finset.card_eq_one.mp hcard
  have htop : F = (⊤ : MatroidFlat M) := by
    simpa only [hF, Finset.sup_singleton, id_eq] using A.2.2.2
  apply Subtype.ext
  exact hF.trans (congrArg singleton htop)

/-- Singleton parallel classes preserve the actual basis count under
simplification. The proof consumes the checked basis/class-choice bijection. -/
theorem simplifiedBasis_count_of_singleton_classes (M : Matroid α)
    (hclasses : ∀ F : MatroidFlat M, MatroidFlat.rank F = 1 →
      (parallelClassElements F).card = 1) :
    Fintype.card (SimplifiedBasis M) = Fintype.card (MatroidBases M) := by
  symm
  calc
    _ = Fintype.card (BasisChoices M) := (Fintype.card_congr basisChoicesEquivBases).symm
    _ = ∑ A : SimplifiedBasis M, Fintype.card (BasisClassChoice A) := Fintype.card_sigma
    _ = ∑ _A : SimplifiedBasis M, 1 := by
      apply Finset.sum_congr rfl
      intro A _
      rw [Fintype.card_pi]
      apply Finset.prod_eq_one
      intro F _
      rw [Fintype.card_coe]
      exact hclasses F.1 (A.2.1 F.1 F.2)
    _ = Fintype.card (SimplifiedBasis M) := by simp

end BooleanAntichainsKernel
