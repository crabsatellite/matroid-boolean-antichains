import BooleanAntichainsKernel.IncidencePlaneFlats
import BooleanAntichainsKernel.SingletonAntichains
import BooleanAntichainsKernel.HeightGapEndpoints

namespace BooleanAntichainsKernel

open Set
open scoped Classical

variable {P L : Type*} [Membership P L] [Configuration.ProjectivePlane P L]
variable [Fintype P] [Fintype L]

/-- An enumeration code for the already identified actual flat sets;
this is used only through the proved bijection below. -/
noncomputable def incidencePlaneFlatOfCode :
    Unit ⊕ P ⊕ L ⊕ Unit → MatroidFlat (incidencePlaneMatroid P L)
  | Sum.inl _ => ⊥
  | Sum.inr (Sum.inl p) => incidencePlanePointFlat p
  | Sum.inr (Sum.inr (Sum.inl l)) => incidencePlaneLineFlat l
  | Sum.inr (Sum.inr (Sum.inr _)) => ⊤

theorem incidencePlaneFlatOfCode_injective : Function.Injective
    (incidencePlaneFlatOfCode (P := P) (L := L)) := by
  intro a b h
  have hr := congrArg (fun F : MatroidFlat (incidencePlaneMatroid P L) ↦ MatroidFlat.rank F) h
  rcases a with ⟨⟩ | p | l | ⟨⟩ <;> rcases b with ⟨⟩ | q | m | ⟨⟩
  all_goals simp only [incidencePlaneFlatOfCode, MatroidFlat.rank_bot, incidencePlanePointFlat_rank,
    incidencePlaneLineFlat_rank, incidencePlaneFlat_top_rank] at hr
  all_goals try omega
  all_goals first
    | rfl
    | exact congrArg (fun p : P ↦ Sum.inr (Sum.inl p)) (incidencePlanePointFlat_injective h)
    | exact congrArg (fun l : L ↦ Sum.inr (Sum.inr (Sum.inl l))) (incidencePlaneLineFlat_injective h)

theorem incidencePlaneFlatOfCode_surjective : Function.Surjective
    (incidencePlaneFlatOfCode (P := P) (L := L)) := by
  intro F
  rcases incidencePlaneMatroid_isFlat_cases F.2 with h0 | ⟨p, hp⟩ | ⟨l, hl⟩ | ht
  · exact ⟨Sum.inl (), Subtype.ext (incidencePlaneFlat_bot_val.trans h0.symm)⟩
  · exact ⟨Sum.inr (Sum.inl p), Subtype.ext hp.symm⟩
  · exact ⟨Sum.inr (Sum.inr (Sum.inl l)), Subtype.ext hl.symm⟩
  · exact ⟨Sum.inr (Sum.inr (Sum.inr ())), Subtype.ext ht.symm⟩

noncomputable def incidencePlaneFlatEquiv :
    (Unit ⊕ P ⊕ L ⊕ Unit) ≃ MatroidFlat (incidencePlaneMatroid P L) :=
  Equiv.ofBijective incidencePlaneFlatOfCode
    ⟨incidencePlaneFlatOfCode_injective, incidencePlaneFlatOfCode_surjective⟩

theorem incidencePlaneFlat_card :
    Fintype.card (MatroidFlat (incidencePlaneMatroid P L)) = Fintype.card P + Fintype.card L + 2 := by
  rw [← Fintype.card_congr (incidencePlaneFlatEquiv (P := P) (L := L))]
  simp only [Fintype.card_sum, Fintype.card_unit]
  omega

theorem incidencePlaneFlat_card_order :
    Fintype.card (MatroidFlat (incidencePlaneMatroid P L)) =
      2 * (Configuration.ProjectivePlane.order P L ^ 2 + Configuration.ProjectivePlane.order P L + 1) + 2 := by
  rw [incidencePlaneFlat_card, plane_card_points (L := L), plane_card_lines (P := P)]
  omega

omit [Fintype L] in
theorem incidencePlane_zero_count :
    Fintype.card (BooleanAntichain 0 (MatroidFlat (incidencePlaneMatroid P L))) = 1 :=
  booleanAntichain_count_zero

theorem incidencePlane_singleton_count :
    Fintype.card (BooleanAntichain 1 (MatroidFlat (incidencePlaneMatroid P L))) =
      2 * (Configuration.ProjectivePlane.order P L ^ 2 + Configuration.ProjectivePlane.order P L + 1) + 1 := by
  rw [singletonAntichain_count,
    Fintype.card_subtype_compl (fun F : MatroidFlat (incidencePlaneMatroid P L) ↦ F = ⊤),
    Fintype.card_subtype_eq, incidencePlaneFlat_card_order]
  omega

end BooleanAntichainsKernel
