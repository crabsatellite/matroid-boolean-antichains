import BooleanAntichainsKernel.MatroidRank

/-! Rank-one flats as the paper's carrier for a simplified matroid basis.
Representatives are chosen only inside their genuine nonloop parallel class.
The manuscript proof of the basis-span lemma proceeds through these actual
matroid bases and the submodular rank inequality. -/

namespace BooleanAntichainsKernel

open Set Finset

variable {α : Type*} [Fintype α] {M : Matroid α}

/-- The representation of a simplified basis fixed in Section 2 of the paper. -/
def IsSimplifiedBasis (M : Matroid α) (A : Finset (MatroidFlat M)) : Prop :=
  (∀ F ∈ A, MatroidFlat.rank F = 1) ∧
  A.card = MatroidFlat.rank (⊤ : MatroidFlat M) ∧ A.sup id = ⊤

lemma rank_one_flat_has_representative (F : MatroidFlat M) (hF : MatroidFlat.rank F = 1) :
    ∃ e ∈ F.1, M.IsNonloop e ∧ M.closure {e} = F.1 := by
  have hr : M.eRk F.1 = 1 := by
    rw [← coe_matroidRank]
    exact_mod_cast hF
  obtain ⟨e, heF, hne, hspan⟩ := (Matroid.eRk_eq_one_iff F.2.subset_ground).mp hr
  refine ⟨e, heF, hne, Set.Subset.antisymm ?_ hspan⟩
  rw [← F.2.closure]
  exact M.closure_subset_closure (singleton_subset_iff.mpr heF)

omit [Fintype α] in
lemma flat_finset_sup_coe {ι : Type*} (A : ι → MatroidFlat M) (S : Finset ι) :
    (S.sup A).1 = M.closure (⋃ i ∈ S, (A i).1) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    rw [Finset.sup_insert]
    change M.closure ((A i).1 ∪ (S.sup A).1) = _
    rw [ih, M.closure_union_closure_right_eq]
    congr 1
    ext x
    simp

omit [Fintype α] in
lemma representative_sup_coe {ι : Type*} (A : ι → MatroidFlat M) (e : ι → α)
    (he : ∀ i, M.closure {e i} = (A i).1) (S : Finset ι) :
    (S.sup A).1 = M.closure (e '' (S : Set ι)) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    rw [Finset.sup_insert]
    change M.closure ((A i).1 ∪ (S.sup A).1) = _
    rw [ih, ← he i,
      M.closure_closure_union_closure_eq_closure_union]
    simp only [Finset.coe_insert, Set.image_insert_eq, Set.singleton_union]

/-- Any choice of representatives of a full-rank rank-one family is a basis
of the actual mathlib matroid; this is not an assumed basis adapter. -/
lemma rank_one_representatives_isBase {r : ℕ} (A : Fin r → MatroidFlat M)
    (hAinj : Function.Injective A) (e : Fin r → α)
    (he : ∀ i, M.closure {e i} = (A i).1)
    (htop : Finset.univ.sup A = ⊤)
    (hr : MatroidFlat.rank (⊤ : MatroidFlat M) = r) :
    M.IsBase (Set.range e) := by
  classical
  have heinj : Function.Injective e := by
    intro i j hij
    apply hAinj
    apply Subtype.ext
    rw [← he i, ← he j, hij]
  have hclosure : M.closure (Set.range e) = M.E := by
    have hs := representative_sup_coe A e he Finset.univ
    rw [htop] at hs
    simpa using hs.symm
  have hcard : (Set.range e).ncard = r := by
    simpa using Set.ncard_range_of_injective heinj
  have hrange : matroidRank M (Set.range e) = r := by
    rw [← matroidRank_closure, hclosure]
    exact hr
  have hind : M.Indep (Set.range e) := by
    apply (Matroid.indep_iff_eRk_eq_encard_of_finite (Set.toFinite _)).mpr
    rw [← coe_matroidRank, ← Set.coe_ncard_eq_encard, hrange, hcard]
  exact hind.isBase_of_ground_subset_closure hclosure.symm.subset

/-- Each join face has the cardinality rank asserted in Lemma 2.2. -/
lemma representative_face_rank {r : ℕ} (A : Fin r → MatroidFlat M)
    (hAinj : Function.Injective A) (e : Fin r → α)
    (he : ∀ i, M.closure {e i} = (A i).1)
    (hb : M.IsBase (Set.range e)) (S : Finset (Fin r)) :
    MatroidFlat.rank (S.sup A) = S.card := by
  have heinj : Function.Injective e := by
    intro i j hij
    apply hAinj
    apply Subtype.ext
    rw [← he i, ← he j, hij]
  change matroidRank M (S.sup A).1 = _
  rw [representative_sup_coe A e he, matroidRank_closure,
    matroidRank_indep (hb.indep.subset (Set.image_subset_range _ _))]
  rw [Set.ncard_image_of_injective _ heinj]
  simp

end BooleanAntichainsKernel
