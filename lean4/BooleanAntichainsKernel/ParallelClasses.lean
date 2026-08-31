import BooleanAntichainsKernel.MaximumBijection
import BooleanAntichainsKernel.TuttePolynomial

/-! The actual nonloop parallel classes and the class family of a matroid
basis, as used in the proof of `thm:weighted`. -/

namespace BooleanAntichainsKernel

open Set Finset
open scoped Classical

variable {α : Type*} [Fintype α] {M : Matroid α}

def elementFlat (M : Matroid α) (e : α) : MatroidFlat M :=
  ⟨M.closure {e}, M.isFlat_closure _⟩

noncomputable def parallelClassElements (F : MatroidFlat M) : Finset α :=
  (F.1 \ M.closure ∅).toFinset

@[simp] lemma mem_parallelClassElements (F : MatroidFlat M) (e : α) :
    e ∈ parallelClassElements F ↔ e ∈ F.1 ∧ e ∉ M.closure ∅ := by
  simp [parallelClassElements]

omit [Fintype α] in
lemma elementFlat_rank_one {e : α} (he : M.IsNonloop e) :
    MatroidFlat.rank (elementFlat M e) = 1 := by
  change (M.eRk (M.closure {e})).toNat = 1
  rw [M.eRk_closure_eq, he.eRk_eq]
  rfl

lemma elementFlat_eq_of_parallelClass {F : MatroidFlat M}
    (hF : MatroidFlat.rank F = 1) {e : α} (he : e ∈ parallelClassElements F) :
    elementFlat M e = F := by
  obtain ⟨heF, heLoop⟩ := (mem_parallelClassElements F e).mp he
  have heN : M.IsNonloop e := (Matroid.isNonloop_iff_notMem_loops (F.2.subset_ground heF)).mpr heLoop
  have hle : elementFlat M e ≤ F := by
    change M.closure {e} ⊆ F.1
    rw [← F.2.closure]
    exact M.closure_subset_closure (Set.singleton_subset_iff.mpr heF)
  exact MatroidFlat.eq_of_le_of_rank_eq hle ((elementFlat_rank_one heN).trans hF.symm)

lemma parallelClassElements_nonempty {F : MatroidFlat M} (hF : MatroidFlat.rank F = 1) :
    (parallelClassElements F).Nonempty := by
  obtain ⟨e, heF, heN, _⟩ := rank_one_flat_has_representative F hF
  exact ⟨e, (mem_parallelClassElements F e).mpr
    ⟨heF, (Matroid.isNonloop_iff_notMem_loops heN.mem_ground).mp heN⟩⟩

lemma parallelClassElements_disjoint {F G : MatroidFlat M}
    (hF : MatroidFlat.rank F = 1) (hG : MatroidFlat.rank G = 1) (hFG : F ≠ G) :
    Disjoint (parallelClassElements F) (parallelClassElements G) := by
  rw [Finset.disjoint_left]
  intro e heF heG
  exact hFG ((elementFlat_eq_of_parallelClass hF heF).symm.trans
    (elementFlat_eq_of_parallelClass hG heG))

omit [Fintype α] in
lemma elementFlat_injOn_indep {I : Set α} (hI : M.Indep I) : Set.InjOn (elementFlat M) I := by
  intro e he f hf heq
  have hset : M.closure {e} = M.closure {f} := congrArg Subtype.val heq
  have hecl : e ∈ M.closure {f} := hset ▸ M.mem_closure_self e (hI.subset_ground he)
  have hinter := hI.closure_inter_eq_self_of_subset (Set.singleton_subset_iff.mpr hf)
  have heint : e ∈ M.closure {f} ∩ I := ⟨hecl, he⟩
  rw [hinter] at heint
  exact Set.mem_singleton_iff.mp heint

noncomputable def basisClassSet (B : Finset α) : Finset (MatroidFlat M) :=
  B.image (elementFlat M)

lemma basisClassSet_card {B : Finset α} (hB : M.IsBase (B : Set α)) :
    (basisClassSet (M := M) B).card = B.card :=
  Finset.card_image_iff.mpr (elementFlat_injOn_indep hB.indep)

lemma basisClassSet_sup (B : Finset α) :
    ((basisClassSet (M := M) B).sup id).1 = M.closure (B : Set α) := by
  rw [basisClassSet, Finset.sup_image]
  have h := representative_sup_coe (elementFlat M) id (fun _ ↦ rfl) B
  simpa using h

theorem basisClassSet_isSimplifiedBasis (B : MatroidBases M) :
    IsSimplifiedBasis M (basisClassSet (M := M) B.1) := by
  refine ⟨?_, ?_, ?_⟩
  · intro F hF
    rcases Finset.mem_image.mp hF with ⟨e, he, rfl⟩
    exact elementFlat_rank_one (B.2.indep.isNonloop_of_mem he)
  · rw [basisClassSet_card B.2]
    obtain ⟨_, hcard, hrank⟩ := (matroid_isBase_iff_rank M B.1).mp B.2
    exact hcard.symm.trans hrank
  · apply Subtype.ext
    rw [basisClassSet_sup, B.2.closure_eq, MatroidFlat.val_top]

noncomputable def basisToSimplifiedBasis (B : MatroidBases M) : SimplifiedBasis M :=
  ⟨basisClassSet (M := M) B.1, basisClassSet_isSimplifiedBasis B⟩

lemma basis_member_parallelClass {B : Finset α} (hB : M.IsBase (B : Set α))
    {e : α} (he : e ∈ B) : e ∈ parallelClassElements (elementFlat M e) := by
  apply (mem_parallelClassElements _ _).mpr
  have heN := hB.indep.isNonloop_of_mem he
  exact ⟨M.mem_closure_self e heN.mem_ground,
    (Matroid.isNonloop_iff_notMem_loops heN.mem_ground).mp heN⟩

end BooleanAntichainsKernel
