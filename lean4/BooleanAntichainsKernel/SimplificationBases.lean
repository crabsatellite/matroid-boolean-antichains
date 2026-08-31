import BooleanAntichainsKernel.MatroidSimplification
import BooleanAntichainsKernel.TuttePolynomial

/-! Exact identification of the paper's finite families of rank-one flats
with the bases of the actual simplification matroid. -/

namespace BooleanAntichainsKernel

open Set Finset
open scoped Classical

variable {α : Type*} [Fintype α] {M : Matroid α}

noncomputable def rankOneFamily (B : Finset (RankOneFlat M)) : Finset (MatroidFlat M) :=
  B.image Subtype.val

lemma rankOneFamily_card (B : Finset (RankOneFlat M)) : (rankOneFamily B).card = B.card :=
  Finset.card_image_of_injective B Subtype.val_injective

lemma rankOneFamily_sup (B : Finset (RankOneFlat M)) :
    (rankOneFamily B).sup id = B.sup (Subtype.val : RankOneFlat M → MatroidFlat M) :=
  Finset.sup_image B Subtype.val id

lemma rankOneFamily_members (B : Finset (RankOneFlat M)) :
    ∀ F ∈ rankOneFamily B, MatroidFlat.rank F = 1 := by
  intro F hF
  rcases Finset.mem_image.mp hF with ⟨q, _, rfl⟩
  exact q.2

lemma actual_simplification_isBase_iff (B : Finset (RankOneFlat M)) :
    (simplificationOnFlats M).IsBase (B : Set (RankOneFlat M)) ↔
      IsSimplifiedBasis M (rankOneFamily B) := by
  have hrank : matroidRank (simplificationOnFlats M) (B : Set (RankOneFlat M)) =
      MatroidFlat.rank ((rankOneFamily B).sup id) := by
    rw [rankOneFamily_sup]
    exact simplificationOnFlats_finset_rank B
  have htotal : matroidRank (simplificationOnFlats M) (simplificationOnFlats M).E =
      MatroidFlat.rank (⊤ : MatroidFlat M) := simplificationOnFlats_total_rank M
  rw [matroid_isBase_iff_rank]
  constructor
  · rintro ⟨_, hcard, heq⟩
    refine ⟨rankOneFamily_members B, ?_, ?_⟩
    · rw [rankOneFamily_card, ← hcard, heq, htotal]
    · apply MatroidFlat.eq_of_le_of_rank_eq le_top
      rw [← hrank, heq, htotal]
  · rintro ⟨_, hcard, hsup⟩
    refine ⟨by rw [simplificationOnFlats_ground]; exact Set.subset_univ _, ?_, ?_⟩
    · rw [hrank, hsup, ← hcard, rankOneFamily_card]
    · rw [hrank, hsup, htotal]

/-- Lift a collection of rank-one flats to the actual simplification ground. -/
noncomputable def liftRankOneFamily (A : Finset (MatroidFlat M)) : Finset (RankOneFlat M) :=
  Finset.univ.filter fun F ↦ F.1 ∈ A

lemma rankOneFamily_lift (A : Finset (MatroidFlat M))
    (hA : ∀ F ∈ A, MatroidFlat.rank F = 1) : rankOneFamily (liftRankOneFamily A) = A := by
  ext F
  constructor
  · intro hF
    rcases Finset.mem_image.mp hF with ⟨q, hq, rfl⟩
    exact (Finset.mem_filter.mp hq).2
  · intro hF
    exact Finset.mem_image.mpr ⟨⟨F, hA F hF⟩,
      Finset.mem_filter.mpr ⟨mem_univ _, hF⟩, rfl⟩

lemma lift_rankOneFamily (B : Finset (RankOneFlat M)) : liftRankOneFamily (rankOneFamily B) = B := by
  ext q
  simp only [liftRankOneFamily, rankOneFamily, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_image]
  constructor
  · rintro ⟨p, hp, heq⟩
    exact (Subtype.ext heq : p = q) ▸ hp
  · intro hq
    exact ⟨q, hq, rfl⟩

noncomputable def simplifiedBasisEquivActualMatroidBases :
    SimplifiedBasis M ≃ MatroidBases (simplificationOnFlats M) where
  toFun A := ⟨liftRankOneFamily A.1, (actual_simplification_isBase_iff _).mpr (by
    rw [rankOneFamily_lift A.1 A.2.1]
    exact A.2)⟩
  invFun B := ⟨rankOneFamily B.1, (actual_simplification_isBase_iff _).mp B.2⟩
  left_inv A := Subtype.ext (rankOneFamily_lift A.1 A.2.1)
  right_inv B := Subtype.ext (lift_rankOneFamily B.1)

theorem simplifiedBasis_count_eq_actualMatroidBases :
    Fintype.card (SimplifiedBasis M) = Fintype.card (MatroidBases (simplificationOnFlats M)) :=
  Fintype.card_congr simplifiedBasisEquivActualMatroidBases

theorem maximumAntichain_count_eq_tutte :
    (Fintype.card (MaximumBooleanAntichain M) : ℤ) =
      MvPolynomial.eval (fun _ : Fin 2 ↦ (1 : ℤ)) (matroidTuttePolynomial (simplificationOnFlats M)) := by
  rw [matroidTutte_at_one_eq_number_of_bases, maximumAntichain_count_eq_simplifiedBases,
    simplifiedBasis_count_eq_actualMatroidBases]

end BooleanAntichainsKernel
