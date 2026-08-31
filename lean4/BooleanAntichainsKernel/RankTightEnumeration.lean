import BooleanAntichainsKernel.RankTightFibers
import BooleanAntichainsKernel.SimplificationBases

/-! The exact bottom-flat partition and corank sum in `cor:rank-tight`. -/

namespace BooleanAntichainsKernel

open Set Finset
open scoped Classical Matroid

variable {α : Type*} [Fintype α]

abbrev RankTightAntichain (M : Matroid α) (k : ℕ) :=
  {C : BooleanAntichain k (MatroidFlat M) // IsRankTight C}

abbrev CorankFlat (M : Matroid α) (k : ℕ) := {X : MatroidFlat M // HasCorank M k X}

noncomputable instance {M : Matroid α} {k : ℕ} : Fintype (RankTightAntichain M k) := Subtype.fintype _
noncomputable instance {M : Matroid α} {k : ℕ} : Fintype (CorankFlat M k) := Subtype.fintype _

variable {M : Matroid α} {k : ℕ}

noncomputable def rankTightBottom (C : RankTightAntichain M k) : CorankFlat M k :=
  ⟨C.1.1.inf id, (hasCorank_bottom_iff_rankTight C.1).mpr C.2⟩

noncomputable def rankTightBottomFiberEquiv (X : CorankFlat M k) :
    {C : RankTightAntichain M k // rankTightBottom C = X} ≃ BottomFlatFiber M k X.1 where
  toFun C := ⟨C.1.1, congrArg Subtype.val C.2⟩
  invFun D := ⟨⟨D.1, (hasCorank_bottom_iff_rankTight D.1).mp (by rw [D.2]; exact X.2)⟩,
    Subtype.ext D.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Every object is placed in the fiber of its literal common meet. -/
noncomputable def rankTightEquivBottomFibers :
    RankTightAntichain M k ≃ Σ X : CorankFlat M k, BottomFlatFiber M k X.1 :=
  (Equiv.sigmaFiberEquiv (rankTightBottom (M := M) (k := k))).symm.trans
    (Equiv.sigmaCongrRight rankTightBottomFiberEquiv)

@[simp] theorem rankTightEquivBottomFibers_index (C : RankTightAntichain M k) :
    (rankTightEquivBottomFibers C).1.1 = C.1.1.inf id := rfl

theorem rankTight_count_by_bottom_subtype (M : Matroid α) (k : ℕ) :
    Fintype.card (RankTightAntichain M k) =
      ∑ X : CorankFlat M k, Fintype.card (SimplifiedBasis (M ／ X.1.1)) := by
  calc
    _ = Fintype.card (Σ X : CorankFlat M k, BottomFlatFiber M k X.1) :=
      Fintype.card_congr rankTightEquivBottomFibers
    _ = ∑ X : CorankFlat M k, Fintype.card (BottomFlatFiber M k X.1) := Fintype.card_sigma
    _ = ∑ X : CorankFlat M k, Fintype.card (SimplifiedBasis (M ／ X.1.1)) := by
      apply Finset.sum_congr rfl
      intro X _
      exact bottomFiber_count_eq_contraction_bases k X.1 X.2

/-- The displayed corank sum, with integer rather than truncated subtraction. -/
theorem rankTight_count (M : Matroid α) (k : ℕ) :
    Fintype.card (RankTightAntichain M k) =
      ∑ X ∈ (Finset.univ.filter (HasCorank M k)),
        Fintype.card (SimplifiedBasis (M ／ X.1)) := by
  rw [rankTight_count_by_bottom_subtype]
  exact (Finset.sum_subtype (Finset.univ.filter (HasCorank M k))
    (fun X ↦ by simp) (fun X : MatroidFlat M ↦ Fintype.card (SimplifiedBasis (M ／ X.1)))).symm

/-- Consume the identification with bases of the actual simplification
matroid, not only the rank-one-flat representation of those bases. -/
noncomputable def bottomFiberEquivActualContractionBases (k : ℕ) (X : MatroidFlat M)
    (hX : HasCorank M k X) :
    BottomFlatFiber M k X ≃ MatroidBases (simplificationOnFlats (M ／ X.1)) :=
  (bottomFiberEquivContractionBases k X hX).trans simplifiedBasisEquivActualMatroidBases

theorem rankTight_count_actual_simplification (M : Matroid α) (k : ℕ) :
    Fintype.card (RankTightAntichain M k) =
      ∑ X ∈ Finset.univ.filter (HasCorank M k),
        Fintype.card (MatroidBases (simplificationOnFlats (M ／ X.1))) := by
  rw [rankTight_count]
  apply Finset.sum_congr rfl
  intro X _
  exact simplifiedBasis_count_eq_actualMatroidBases

theorem corankFilter_empty_above_rank (M : Matroid α) (k : ℕ)
    (hk : MatroidFlat.rank (⊤ : MatroidFlat M) < k) :
    Finset.univ.filter (HasCorank M k) = ∅ := by
  apply Finset.filter_eq_empty_iff.mpr
  intro X _ hX
  have hx := (hasCorank_iff_add k X).mp hX
  omega

theorem rankTight_count_above_rank (M : Matroid α) (k : ℕ)
    (hk : MatroidFlat.rank (⊤ : MatroidFlat M) < k) :
    Fintype.card (RankTightAntichain M k) = 0 := by
  rw [rankTight_count, corankFilter_empty_above_rank M k hk]
  simp

end BooleanAntichainsKernel
