import BooleanAntichainsKernel.MaximumBijection

/-! A mathlib matroid model of the paper's simplification, with rank-one
flats as its actual elements.  One nonloop representative from each class
gives a comap matroid; all ground and rank transports are proved here. -/

namespace BooleanAntichainsKernel

open Set Finset

variable {α : Type*} [Fintype α]

abbrev RankOneFlat (M : Matroid α) := {F : MatroidFlat M // MatroidFlat.rank F = 1}

noncomputable instance {M : Matroid α} : Fintype (RankOneFlat M) := by
  classical
  exact Subtype.fintype _

noncomputable instance {M : Matroid α} : DecidableEq (RankOneFlat M) := Classical.decEq _

noncomputable def rankOneRepresentative {M : Matroid α} (F : RankOneFlat M) : α :=
  (rank_one_flat_has_representative F.1 F.2).choose

lemma rankOneRepresentative_spec {M : Matroid α} (F : RankOneFlat M) :
    rankOneRepresentative F ∈ F.1.1 ∧ M.IsNonloop (rankOneRepresentative F) ∧
      M.closure {rankOneRepresentative F} = F.1.1 :=
  (rank_one_flat_has_representative F.1 F.2).choose_spec

lemma rankOneRepresentative_injective {M : Matroid α} :
    Function.Injective (rankOneRepresentative (M := M)) := by
  intro F G hFG
  apply Subtype.ext
  apply Subtype.ext
  rw [← (rankOneRepresentative_spec F).2.2, ← (rankOneRepresentative_spec G).2.2, hFG]

noncomputable def simplificationOnFlats (M : Matroid α) : Matroid (RankOneFlat M) :=
  M.comap rankOneRepresentative

lemma rankOneRepresentative_mem_ground {M : Matroid α} (F : RankOneFlat M) :
    rankOneRepresentative F ∈ M.E := (rankOneRepresentative_spec F).2.1.mem_ground

@[simp] lemma simplificationOnFlats_ground (M : Matroid α) :
    (simplificationOnFlats M).E = Set.univ := by
  ext F
  simp only [simplificationOnFlats, Matroid.comap_ground_eq, Set.mem_preimage, Set.mem_univ, iff_true]
  exact rankOneRepresentative_mem_ground F

lemma rankOneRepresentatives_span (M : Matroid α) :
    M.closure (Set.range (rankOneRepresentative (M := M))) = M.E := by
  apply Set.Subset.antisymm (M.closure_subset_ground _)
  intro e heE
  by_cases heLoop : e ∈ M.closure ∅
  · exact M.closure_subset_closure (Set.empty_subset _) heLoop
  have he : M.IsNonloop e := (Matroid.isNonloop_iff_notMem_loops heE).mpr heLoop
  let F : MatroidFlat M := ⟨M.closure {e}, M.isFlat_closure _⟩
  have hF : MatroidFlat.rank F = 1 := by
    change (M.eRk (M.closure {e})).toNat = 1
    rw [M.eRk_closure_eq, he.eRk_eq]
    rfl
  let A : RankOneFlat M := ⟨F, hF⟩
  have heF : e ∈ F.1 := M.mem_closure_self e heE
  have hrep : M.closure {rankOneRepresentative A} = F.1 := (rankOneRepresentative_spec A).2.2
  rw [← hrep] at heF
  have hsub : {rankOneRepresentative A} ⊆ Set.range (rankOneRepresentative (M := M)) :=
    Set.singleton_subset_iff.mpr ⟨A, rfl⟩
  exact M.closure_subset_closure hsub heF

lemma simplificationOnFlats_rank (M : Matroid α) (X : Set (RankOneFlat M)) :
    matroidRank (simplificationOnFlats M) X = matroidRank M (rankOneRepresentative '' X) := by
  unfold matroidRank simplificationOnFlats
  rw [Matroid.eRk_comap]

lemma simplificationOnFlats_total_rank (M : Matroid α) :
    matroidRank (simplificationOnFlats M) (simplificationOnFlats M).E = matroidRank M M.E := by
  rw [simplificationOnFlats_ground, simplificationOnFlats_rank, Set.image_univ,
    ← matroidRank_closure, rankOneRepresentatives_span]

lemma simplificationOnFlats_isBase_iff {M : Matroid α} (B : Set (RankOneFlat M)) :
    (simplificationOnFlats M).IsBase B ↔ M.IsBase (rankOneRepresentative '' B) := by
  have hground : rankOneRepresentative (M := M) ⁻¹' M.E = Set.univ :=
    simplificationOnFlats_ground M
  have hspan : M.Spanning (Set.range (rankOneRepresentative (M := M))) :=
    (Matroid.spanning_iff_closure_eq (by
      rintro _ ⟨F, rfl⟩
      exact rankOneRepresentative_mem_ground F)).mpr (rankOneRepresentatives_span M)
  rw [simplificationOnFlats, Matroid.comap_isBase_iff, hground, Set.image_univ]
  constructor
  · rintro ⟨hB, _, _⟩
    exact hB.isBase_of_spanning hspan
  · intro hB
    exact ⟨hB.isBasis_of_subset hspan.subset_ground (Set.image_subset_range _ _),
      rankOneRepresentative_injective.injOn, Set.subset_univ _⟩

lemma simplificationOnFlats_finset_rank {M : Matroid α} (B : Finset (RankOneFlat M)) :
    matroidRank (simplificationOnFlats M) (B : Set (RankOneFlat M)) =
      MatroidFlat.rank (B.sup (Subtype.val : RankOneFlat M → MatroidFlat M)) := by
  rw [simplificationOnFlats_rank]
  change matroidRank M _ = matroidRank M (B.sup Subtype.val).1
  rw [representative_sup_coe (fun F : RankOneFlat M ↦ F.1) rankOneRepresentative
    (fun F ↦ (rankOneRepresentative_spec F).2.2), matroidRank_closure]

end BooleanAntichainsKernel
