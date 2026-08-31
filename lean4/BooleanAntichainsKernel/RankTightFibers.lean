import BooleanAntichainsKernel.UpperIntervalAntichains
import BooleanAntichainsKernel.IntervalTheorem
import BooleanAntichainsKernel.RankProfiles

namespace BooleanAntichainsKernel

open Set Finset
open scoped Classical Matroid

variable {α : Type*} [Fintype α] {M : Matroid α}

/-- The manuscript corank condition with ordinary integer subtraction.
Unlike natural subtraction, it gives an empty layer when `k > rank M`. -/
def HasCorank (M : Matroid α) (k : ℕ) (X : MatroidFlat M) : Prop :=
  (MatroidFlat.rank X : ℤ) = (MatroidFlat.rank (⊤ : MatroidFlat M) : ℤ) - (k : ℤ)

omit [Fintype α] in
lemma hasCorank_iff_add (k : ℕ) (X : MatroidFlat M) :
    HasCorank M k X ↔ MatroidFlat.rank X + k = MatroidFlat.rank (⊤ : MatroidFlat M) := by
  unfold HasCorank
  omega

lemma booleanAntichain_bottom_rank_bound {k : ℕ} (C : BooleanAntichain k (MatroidFlat M)) :
    MatroidFlat.rank (C.1.inf id) + k ≤ MatroidFlat.rank (⊤ : MatroidFlat M) := by
  let e := canonicalEnumeration C
  let H : Fin k → MatroidFlat M := fun i ↦ (e i).1
  have hH : IsBooleanTuple H := (isBooleanTuple_iff_antichain_of_equiv C.1 e).mpr C.2.2
  have hb := (boolean_face_rank_bounds hH MatroidFlat.rank MatroidFlat.rank_strictMono Finset.univ).1
  have heq : commonMeet H = C.1.inf id := enumeration_commonMeet C.1 e
  simpa only [heq, meetFace_univ, Finset.card_univ, Fintype.card_fin] using hb

theorem hasCorank_bottom_iff_rankTight {k : ℕ} (C : BooleanAntichain k (MatroidFlat M)) :
    HasCorank M k (C.1.inf id) ↔ IsRankTight C := by
  rw [hasCorank_iff_add]
  have hb := booleanAntichain_bottom_rank_bound C
  unfold IsRankTight
  omega

lemma intervalAntichain_bottom (X Y : MatroidFlat M) [Fact (X ≤ Y)]
    (D : IntervalBooleanAntichain X Y) : (D.1.inf id).1 = X := by
  let e := canonicalEnumeration D
  let H : Fin (MatroidFlat.rank Y - MatroidFlat.rank X) → FlatInterval X Y := fun i ↦ (e i).1
  let ρ : FlatInterval X Y → ℕ := fun F ↦ MatroidFlat.rank F.1
  have hρ : StrictMono ρ := fun _ _ h ↦ MatroidFlat.rank_strictMono h
  have hH : IsBooleanTuple H := (isBooleanTuple_iff_antichain_of_equiv D.1 e).mpr D.2.2
  have hb := (boolean_face_rank_bounds hH ρ hρ Finset.univ).1
  have hc : commonMeet H = D.1.inf id := enumeration_commonMeet D.1 e
  rw [hc] at hb
  simp only [meetFace_univ, Finset.card_univ, Fintype.card_fin] at hb
  change MatroidFlat.rank (D.1.inf id).1 + (MatroidFlat.rank Y - MatroidFlat.rank X) ≤
    MatroidFlat.rank Y at hb
  have hlo : MatroidFlat.rank X ≤ MatroidFlat.rank (D.1.inf id).1 := MatroidFlat.rank_mono (D.1.inf id).2.1
  have hxy : MatroidFlat.rank X ≤ MatroidFlat.rank Y := MatroidFlat.rank_mono Fact.out
  exact (MatroidFlat.eq_of_le_of_rank_eq (D.1.inf id).2.1 (by omega)).symm

abbrev BottomFlatFiber (M : Matroid α) (k : ℕ) (X : MatroidFlat M) :=
  {C : BooleanAntichain k (MatroidFlat M) // C.1.inf id = X}

noncomputable instance {k : ℕ} {X : MatroidFlat M} : Fintype (BottomFlatFiber M k X) :=
  Subtype.fintype _

local instance (X : MatroidFlat M) : Fact (X ≤ (⊤ : MatroidFlat M)) := ⟨le_top⟩

/-- For a fixed corank-k bottom, the actual ambient fiber is exactly the
maximum-antichain family in `[X, top]`. -/
noncomputable def bottomFiberEquivInterval (k : ℕ) (X : MatroidFlat M) (hX : HasCorank M k X) :
    BottomFlatFiber M k X ≃ IntervalBooleanAntichain X (⊤ : MatroidFlat M) := by
  have hkd : k = MatroidFlat.rank (⊤ : MatroidFlat M) - MatroidFlat.rank X := by
    have h := (hasCorank_iff_add k X).mp hX
    omega
  refine
    { toFun := fun C ↦ booleanAntichainSizeEquiv (L := FlatInterval X (⊤ : MatroidFlat M)) hkd
        (liftUpperIntervalAntichain X C.1 C.2.ge)
      invFun := fun D ↦ ⟨booleanAntichainSizeEquiv (L := MatroidFlat M) hkd.symm
        (forgetUpperIntervalAntichain X D), ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · change (forgetUpperIntervalFamily X D.1).inf id = X
    rw [forgetUpperIntervalFamily_inf]
    exact intervalAntichain_bottom X ⊤ D
  · intro C
    apply Subtype.ext
    apply Subtype.ext
    exact forget_liftUpperIntervalFamily X C.1.1 (fun a ha ↦ C.2.ge.trans (Finset.inf_le ha))
  · intro D
    apply Subtype.ext
    exact lift_forgetUpperIntervalFamily X D.1

omit [Fintype α] in
lemma flatIntervalMinor_top_eq_contract (X : MatroidFlat M) :
    flatIntervalMinor X (⊤ : MatroidFlat M) = M ／ X.1 := by
  rw [flatIntervalMinor, MatroidFlat.val_top, Matroid.restrict_ground_eq_self]

/-- The paper's fixed-bottom bijection, literally consuming `thm:interval`
and the equality of its top-restriction minor with `M / X`. -/
noncomputable def bottomFiberEquivContractionBases (k : ℕ) (X : MatroidFlat M)
    (hX : HasCorank M k X) : BottomFlatFiber M k X ≃ SimplifiedBasis (M ／ X.1) :=
  (bottomFiberEquivInterval k X hX).trans
    ((intervalAntichainEquivBasis X (⊤ : MatroidFlat M)).trans
      (Equiv.cast (congrArg (fun N : Matroid α ↦ SimplifiedBasis N) (flatIntervalMinor_top_eq_contract X))))

theorem bottomFiber_count_eq_contraction_bases (k : ℕ) (X : MatroidFlat M) (hX : HasCorank M k X) :
    Fintype.card (BottomFlatFiber M k X) = Fintype.card (SimplifiedBasis (M ／ X.1)) :=
  Fintype.card_congr (bottomFiberEquivContractionBases k X hX)

end BooleanAntichainsKernel
