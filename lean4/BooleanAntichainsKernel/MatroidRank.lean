import BooleanAntichainsKernel.MatroidFlats
import Mathlib.Order.Grade

/-! The manuscript's ordinary natural-number matroid rank, and its grading
of the literal lattice of flats.  Finiteness discharges every `ENat.toNat`
guard; no rank identity is supplied as an external premise. -/

namespace BooleanAntichainsKernel

open Set

variable {α : Type*} [Fintype α]

noncomputable def matroidRank (M : Matroid α) (X : Set α) : ℕ := (M.eRk X).toNat

lemma coe_matroidRank (M : Matroid α) (X : Set α) :
    (matroidRank M X : ℕ∞) = M.eRk X :=
  ENat.coe_toNat (M.isRkFinite_of_finite (Set.toFinite X)).eRk_lt_top.ne

lemma matroidRank_mono (M : Matroid α) : Monotone (matroidRank M) := by
  intro X Y hXY
  apply ENat.coe_le_coe.mp
  simpa only [coe_matroidRank] using M.eRk_mono hXY

omit [Fintype α] in
@[simp] lemma matroidRank_closure (M : Matroid α) (X : Set α) :
    matroidRank M (M.closure X) = matroidRank M X := by
  simp [matroidRank]

omit [Fintype α] in
@[simp] lemma matroidRank_empty (M : Matroid α) : matroidRank M ∅ = 0 := by
  simp [matroidRank]

lemma matroidRank_submod (M : Matroid α) (X Y : Set α) :
    matroidRank M (X ∩ Y) + matroidRank M (X ∪ Y) ≤
      matroidRank M X + matroidRank M Y := by
  apply ENat.coe_le_coe.mp
  simpa only [Nat.cast_add, coe_matroidRank] using M.eRk_submod X Y

lemma matroidRank_indep {M : Matroid α} {I : Set α} (hI : M.Indep I) :
    matroidRank M I = I.ncard := by
  apply ENat.coe_inj.mp
  rw [coe_matroidRank, hI.eRk_eq_encard, Set.coe_ncard_eq_encard]

namespace MatroidFlat

variable {M : Matroid α}

noncomputable def rank (F : MatroidFlat M) : ℕ := matroidRank M F.1

omit [Fintype α] in
@[simp] lemma rank_bot : rank (⊥ : MatroidFlat M) = 0 := by
  change matroidRank M (M.closure ∅) = 0
  simp

lemma rank_mono : Monotone (rank (M := M)) := fun _ _ h ↦ matroidRank_mono M h

lemma rank_strictMono : StrictMono (rank (M := M)) := by
  intro F G hFG
  apply lt_of_le_of_ne (rank_mono hFG.le)
  intro hr
  have her : M.eRk G.1 ≤ M.eRk F.1 := by
    rw [← coe_matroidRank, ← coe_matroidRank]
    exact_mod_cast hr.symm.le
  have hfin := M.isRkFinite_of_finite (Set.toFinite F.1)
  have hcl := hfin.closure_eq_closure_of_subset_of_eRk_ge_eRk hFG.le her
  rw [F.2.closure, G.2.closure] at hcl
  exact hFG.ne (Subtype.ext hcl)

lemma eq_of_le_of_rank_eq {F G : MatroidFlat M} (hFG : F ≤ G)
    (hr : rank F = rank G) : F = G := by
  by_contra hne
  exact (rank_strictMono (lt_of_le_of_ne hFG hne)).ne hr

lemma rank_submod (F G : MatroidFlat M) :
    rank (F ⊓ G) + rank (F ⊔ G) ≤ rank F + rank G := by
  change matroidRank M (F.1 ∩ G.1) + matroidRank M (M.closure (F.1 ∪ G.1)) ≤ _
  rw [matroidRank_closure]
  exact matroidRank_submod M F.1 G.1

lemma rank_covBy {F G : MatroidFlat M} (hFG : F ⋖ G) : rank G = rank F + 1 := by
  have hnot : ¬ G.1 ⊆ F.1 := fun h ↦ hFG.lt.not_ge h
  obtain ⟨e, heG, heF⟩ := Set.not_subset.mp hnot
  let C : MatroidFlat M := ⟨M.closure (insert e F.1), M.isFlat_closure _⟩
  have hFC : F ≤ C := M.subset_closure_of_subset (subset_insert _ _) (by
    exact insert_subset (G.2.subset_ground heG) F.2.subset_ground)
  have heC : e ∈ C.1 := M.mem_closure_of_mem (mem_insert e F.1) (by
    exact insert_subset (G.2.subset_ground heG) F.2.subset_ground)
  have hFC' : F < C := lt_of_le_of_ne hFC (fun h ↦ heF (h ▸ heC))
  have hCG : C ≤ G := by
    change M.closure (insert e F.1) ⊆ G.1
    rw [← G.2.closure]
    exact M.closure_subset_closure (insert_subset heG hFG.le)
  have hCe : C = G := hCG.eq_or_lt.resolve_right (hFG.2 hFC')
  have hstep : M.eRk (insert e F.1) = M.eRk F.1 + 1 :=
    Matroid.eRk_insert_eq_add_one ⟨G.2.subset_ground heG, by simpa [F.2.closure]⟩
  rw [← hCe]
  change matroidRank M (M.closure (insert e F.1)) = matroidRank M F.1 + 1
  rw [matroidRank_closure]
  apply ENat.coe_inj.mp
  simpa only [Nat.cast_add, Nat.cast_one, coe_matroidRank] using hstep

noncomputable instance : GradeMinOrder ℕ (MatroidFlat M) where
  grade := rank
  grade_strictMono := rank_strictMono
  covBy_grade _ _ h := by rw [rank_covBy h]; exact Order.covBy_succ _
  isMin_grade F hF := by
    have hf : F = ⊥ := hF.eq_bot
    rw [hf, rank_bot]
    exact isMin_bot

@[simp] lemma grade_eq_rank (F : MatroidFlat M) : grade ℕ F = rank F := rfl

end MatroidFlat
end BooleanAntichainsKernel
