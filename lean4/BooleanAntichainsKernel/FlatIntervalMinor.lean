import BooleanAntichainsKernel.MinorRank
import Mathlib.Order.LatticeIntervals

namespace BooleanAntichainsKernel

open Set
open scoped Matroid Classical

variable {α : Type*} [Fintype α] {M : Matroid α}

abbrev FlatInterval (X Y : MatroidFlat M) := Set.Icc X Y

noncomputable instance {X Y : MatroidFlat M} : Fintype (FlatInterval X Y) := Subtype.fintype _

/-- The exact restriction/contraction minor in the manuscript. -/
noncomputable def flatIntervalMinor (X Y : MatroidFlat M) : Matroid α := (M ↾ Y.1) ／ X.1

omit [Fintype α] in
@[simp] lemma flatIntervalMinor_ground (X Y : MatroidFlat M) :
    (flatIntervalMinor X Y).E = Y.1 \ X.1 := rfl

lemma flatIntervalMinor_rank (X Y : MatroidFlat M) (hXY : X ≤ Y) {S : Set α}
    (hS : S ⊆ Y.1 \ X.1) :
    matroidRank (flatIntervalMinor X Y) S = matroidRank M (S ∪ X.1) - matroidRank M X.1 := by
  rw [flatIntervalMinor, matroidRank_contract _ hXY hS,
    matroidRank_restrict M (Set.union_subset (hS.trans Set.sdiff_subset) hXY),
    matroidRank_restrict M hXY]

lemma flatIntervalMinor_total_rank (X Y : MatroidFlat M) (hXY : X ≤ Y) :
    MatroidFlat.rank (⊤ : MatroidFlat (flatIntervalMinor X Y)) =
      MatroidFlat.rank Y - MatroidFlat.rank X := by
  change matroidRank (flatIntervalMinor X Y) (flatIntervalMinor X Y).E = _
  rw [flatIntervalMinor_ground, flatIntervalMinor_rank X Y hXY (Set.Subset.refl _),
    Set.sdiff_union_of_subset hXY]
  rfl

/-- The literal forward flat map `F ↦ F \ X`. -/
def flatIntervalToMinor (X Y : MatroidFlat M) (F : FlatInterval X Y) :
    MatroidFlat (flatIntervalMinor X Y) := by
  refine ⟨F.1.1 \ X.1, ?_⟩
  apply Matroid.isFlat_iff_closure_eq.mpr
  rw [flatIntervalMinor, Matroid.contract_closure_eq, Set.sdiff_union_of_subset F.2.1,
    M.restrict_closure_eq F.2.2 Y.2.subset_ground, F.1.2.closure,
    Set.inter_eq_left.mpr F.2.2]

/-- The literal inverse flat map `S ↦ S ∪ X`. -/
def minorToFlatInterval (X Y : MatroidFlat M) (hXY : X ≤ Y)
    (S : MatroidFlat (flatIntervalMinor X Y)) : FlatInterval X Y := by
  have hS : S.1 ⊆ Y.1 \ X.1 := S.2.subset_ground
  have hU : S.1 ∪ X.1 ⊆ Y.1 := Set.union_subset (hS.trans Set.sdiff_subset) hXY
  have hclY : M.closure (S.1 ∪ X.1) ⊆ Y.1 := by
    rw [← Y.2.closure]
    exact M.closure_subset_closure hU
  have hXcl : X.1 ⊆ M.closure (S.1 ∪ X.1) :=
    Set.subset_union_right.trans (M.subset_closure _ (hU.trans Y.2.subset_ground))
  have hN := S.2.closure
  change ((M ↾ Y.1) ／ X.1).closure S.1 = S.1 at hN
  rw [Matroid.contract_closure_eq,
    M.restrict_closure_eq hU Y.2.subset_ground, Set.inter_eq_left.mpr hclY] at hN
  have hclosed : M.closure (S.1 ∪ X.1) = S.1 ∪ X.1 := by
    calc
      _ = (M.closure (S.1 ∪ X.1) \ X.1) ∪ X.1 := (Set.sdiff_union_of_subset hXcl).symm
      _ = S.1 ∪ X.1 := congrArg (fun T : Set α ↦ T ∪ X.1) hN
  exact ⟨⟨S.1 ∪ X.1, Matroid.isFlat_iff_closure_eq.mpr hclosed⟩, Set.subset_union_right, hU⟩

omit [Fintype α] in
theorem flatInterval_minor_left_inverse (X Y : MatroidFlat M) (hXY : X ≤ Y)
    (F : FlatInterval X Y) : minorToFlatInterval X Y hXY (flatIntervalToMinor X Y F) = F := by
  apply Subtype.ext
  apply Subtype.ext
  change (F.1.1 \ X.1) ∪ X.1 = F.1.1
  exact Set.sdiff_union_of_subset F.2.1

omit [Fintype α] in
theorem flatInterval_minor_right_inverse (X Y : MatroidFlat M) (hXY : X ≤ Y)
    (S : MatroidFlat (flatIntervalMinor X Y)) :
    flatIntervalToMinor X Y (minorToFlatInterval X Y hXY S) = S := by
  apply Subtype.ext
  change (S.1 ∪ X.1) \ X.1 = S.1
  ext e
  constructor
  · rintro ⟨heS | heX, hnX⟩
    · exact heS
    · exact (hnX heX).elim
  · intro heS
    exact ⟨Or.inl heS, (S.2.subset_ground heS).2⟩

/-- The canonical flat-lattice isomorphism used by `thm:interval`. -/
def flatIntervalMinorOrderIso (X Y : MatroidFlat M) (hXY : X ≤ Y) :
    FlatInterval X Y ≃o MatroidFlat (flatIntervalMinor X Y) where
  toFun := flatIntervalToMinor X Y
  invFun := minorToFlatInterval X Y hXY
  left_inv := flatInterval_minor_left_inverse X Y hXY
  right_inv := flatInterval_minor_right_inverse X Y hXY
  map_rel_iff' := by
    intro F G
    change F.1.1 \ X.1 ⊆ G.1.1 \ X.1 ↔ F.1.1 ⊆ G.1.1
    constructor
    · intro h e heF
      by_cases heX : e ∈ X.1
      · exact G.2.1 heX
      · exact (h ⟨heF, heX⟩).1
    · intro h e he
      exact ⟨h he.1, he.2⟩

omit [Fintype α] in
lemma flatIntervalMinor_loops_empty (X Y : MatroidFlat M) (hXY : X ≤ Y) :
    (flatIntervalMinor X Y).closure ∅ = ∅ := by
  rw [flatIntervalMinor, Matroid.contract_closure_eq, Set.empty_union,
    M.restrict_closure_eq hXY Y.2.subset_ground, X.2.closure,
    Set.inter_eq_left.mpr hXY, Set.sdiff_self]

omit [Fintype α] in
/-- The exact class factor in the interval-weighted formula. -/
lemma flatInterval_minor_class (X Y : MatroidFlat M) (hXY : X ≤ Y) (F : FlatInterval X Y) :
    (flatIntervalToMinor X Y F).1 \ (flatIntervalMinor X Y).closure ∅ = F.1.1 \ X.1 := by
  rw [flatIntervalMinor_loops_empty X Y hXY, Set.sdiff_empty]
  rfl

end BooleanAntichainsKernel
