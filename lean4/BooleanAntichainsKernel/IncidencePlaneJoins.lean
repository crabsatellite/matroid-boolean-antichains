import BooleanAntichainsKernel.IncidencePlaneFlatCounting
import BooleanAntichainsKernel.MobiusFormula

namespace BooleanAntichainsKernel

open scoped Classical

variable {P L : Type*} [Membership P L] [Configuration.ProjectivePlane P L]
variable [Fintype P] [Fintype L]

@[simp] theorem incidencePlanePointFlat_ne_top (p : P) :
    incidencePlanePointFlat (L := L) p ≠ ⊤ := by
  intro h
  have hr := congrArg MatroidFlat.rank h
  rw [incidencePlanePointFlat_rank, incidencePlaneFlat_top_rank] at hr
  omega

@[simp] theorem incidencePlaneLineFlat_ne_top (l : L) :
    incidencePlaneLineFlat (P := P) l ≠ ⊤ := by
  intro h
  have hr := congrArg MatroidFlat.rank h
  rw [incidencePlaneLineFlat_rank, incidencePlaneFlat_top_rank] at hr
  omega

@[simp] theorem incidencePlane_bot_ne_top :
    (⊥ : MatroidFlat (incidencePlaneMatroid P L)) ≠ ⊤ := by
  intro h
  have hr := congrArg MatroidFlat.rank h
  rw [MatroidFlat.rank_bot, incidencePlaneFlat_top_rank] at hr
  omega

theorem incidencePlaneLineFlat_le_iff (l m : L) :
    incidencePlaneLineFlat (P := P) l ≤ incidencePlaneLineFlat m ↔ l = m := by
  constructor
  · intro h
    exact incidencePlaneLineFlat_injective (MatroidFlat.eq_of_le_of_rank_eq h (by
      rw [incidencePlaneLineFlat_rank, incidencePlaneLineFlat_rank]))
  · rintro rfl
    exact le_rfl

theorem incidencePlane_sup_top_of_rank_two
    (F G : MatroidFlat (incidencePlaneMatroid P L)) (hF : MatroidFlat.rank F = 2)
    (hnot : ¬ G ≤ F) : F ⊔ G = ⊤ := by
  have hstrict : F < F ⊔ G := lt_of_le_of_ne le_sup_left (by
    intro h
    exact hnot (h.symm ▸ (le_sup_right : G ≤ F ⊔ G)))
  have hlo := MatroidFlat.rank_strictMono hstrict
  have hhi := MatroidFlat.rank_mono (le_top : F ⊔ G ≤ ⊤)
  apply MatroidFlat.eq_of_le_of_rank_eq le_top
  rw [hF] at hlo
  rw [incidencePlaneFlat_top_rank] at hhi ⊢
  omega

@[simp] theorem incidencePlane_line_sup_line_eq_top_iff (l m : L) :
    incidencePlaneLineFlat (P := P) l ⊔ incidencePlaneLineFlat m = ⊤ ↔ l ≠ m := by
  constructor
  · intro h hlm
    subst m
    exact incidencePlaneLineFlat_ne_top l (by simpa only [sup_idem] using h)
  · intro hne
    apply incidencePlane_sup_top_of_rank_two _ _ (incidencePlaneLineFlat_rank l)
    intro hle
    exact hne ((incidencePlaneLineFlat_le_iff m l).mp hle).symm

@[simp] theorem incidencePlane_point_sup_line_eq_top_iff (p : P) (l : L) :
    incidencePlanePointFlat (L := L) p ⊔ incidencePlaneLineFlat l = ⊤ ↔ p ∉ l := by
  constructor
  · intro h hp
    have heq := sup_eq_right.mpr ((incidencePlanePointFlat_le_lineFlat p l).mpr hp)
    exact incidencePlaneLineFlat_ne_top l (heq.symm.trans h)
  · intro hp
    rw [sup_comm]
    apply incidencePlane_sup_top_of_rank_two _ _ (incidencePlaneLineFlat_rank l)
    exact fun h ↦ hp ((incidencePlanePointFlat_le_lineFlat p l).mp h)

@[simp] theorem incidencePlane_line_sup_point_eq_top_iff (l : L) (p : P) :
    incidencePlaneLineFlat (P := P) l ⊔ incidencePlanePointFlat p = ⊤ ↔ p ∉ l := by
  rw [sup_comm]
  exact incidencePlane_point_sup_line_eq_top_iff p l

@[simp] theorem incidencePlane_point_sup_point_ne_top (p q : P) :
    incidencePlanePointFlat (L := L) p ⊔ incidencePlanePointFlat q ≠ ⊤ := by
  intro h
  have hs := MatroidFlat.rank_submod (incidencePlanePointFlat (L := L) p) (incidencePlanePointFlat q)
  rw [incidencePlanePointFlat_rank, incidencePlanePointFlat_rank, h, incidencePlaneFlat_top_rank] at hs
  omega

end BooleanAntichainsKernel
