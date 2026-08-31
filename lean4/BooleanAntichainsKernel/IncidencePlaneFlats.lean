import BooleanAntichainsKernel.IncidencePlaneClosure

namespace BooleanAntichainsKernel

open Set
open scoped Classical

variable {P L : Type*} [Membership P L] [Configuration.ProjectivePlane P L] [Fintype P]

/-- Every actual matroid flat has exactly one of the four kinds of point
sets in the plane lattice. This is derived from its actual basis and closure. -/
theorem incidencePlaneMatroid_isFlat_cases {F : Set P}
    (hF : (incidencePlaneMatroid P L).IsFlat F) :
    F = ∅ ∨ (∃ p : P, F = {p}) ∨ (∃ l : L, F = planeLineSet l) ∨ F = univ := by
  obtain ⟨B, hB⟩ := (incidencePlaneMatroid P L).exists_isBasis F (by simp)
  have hcl : (incidencePlaneMatroid P L).closure B = F := hB.closure_eq_closure.trans hF.closure
  have hbound := ((incidencePlaneMatroid_indep_iff P L B).mp hB.indep).1
  have hcases : B.ncard = 0 ∨ B.ncard = 1 ∨ B.ncard = 2 ∨ B.ncard = 3 := by omega
  rcases hcases with h0 | h1 | h2 | h3
  · have hB0 : B = ∅ := (Set.ncard_eq_zero (s := B)).mp h0
    subst B
    exact Or.inl (hcl.symm.trans incidencePlaneMatroid_closure_empty)
  · obtain ⟨p, rfl⟩ := Set.ncard_eq_one.mp h1
    exact Or.inr (Or.inl ⟨p, hcl.symm.trans (incidencePlaneMatroid_closure_singleton p)⟩)
  · obtain ⟨a, b, hab, rfl⟩ := Set.ncard_eq_two.mp h2
    have hline := Configuration.HasLines.mkLine_ax (P := P) (L := L) hab
    exact Or.inr (Or.inr (Or.inl ⟨Configuration.HasLines.mkLine (L := L) hab,
      hcl.symm.trans (incidencePlaneMatroid_closure_pair hab hline.1 hline.2)⟩))
  · exact Or.inr (Or.inr (Or.inr (hcl.symm.trans (incidencePlaneMatroid_closure_three hB.indep h3))))

noncomputable def incidencePlanePointFlat (p : P) : MatroidFlat (incidencePlaneMatroid P L) :=
  ⟨{p}, Matroid.isFlat_iff_closure_eq.mpr (incidencePlaneMatroid_closure_singleton p)⟩

@[simp] theorem incidencePlanePointFlat_val (p : P) :
    (incidencePlanePointFlat (L := L) p).1 = {p} := rfl

theorem incidencePlanePointFlat_rank (p : P) : MatroidFlat.rank (incidencePlanePointFlat (L := L) p) = 1 := by
  change matroidRank (incidencePlaneMatroid P L) {p} = 1
  rw [matroidRank_indep (incidencePlaneMatroid_indep_singleton p), Set.ncard_singleton]

theorem incidencePlanePointFlat_injective :
    Function.Injective (incidencePlanePointFlat (P := P) (L := L)) := by
  intro p q h
  have hs : ({p} : Set P) = {q} := congrArg Subtype.val h
  exact Set.singleton_injective hs

@[simp] theorem incidencePlaneFlat_bot_val :
    (⊥ : MatroidFlat (incidencePlaneMatroid P L)).1 = ∅ := incidencePlaneMatroid_closure_empty

variable [Fintype L]

theorem incidencePlaneMatroid_isFlat_line (l : L) :
    (incidencePlaneMatroid P L).IsFlat (planeLineSet l) := by
  obtain ⟨a, ha, b, hb, hab⟩ := planeLineSet_has_pair (P := P) l
  rw [← incidencePlaneMatroid_closure_pair (l := l) hab ha hb]
  exact (incidencePlaneMatroid P L).isFlat_closure {a, b}

/-- The carrier identification is an iff on the original point sets,
not an equinumerous four-layer replacement of the flat lattice. -/
theorem incidencePlaneMatroid_isFlat_iff (F : Set P) :
    (incidencePlaneMatroid P L).IsFlat F ↔
      F = ∅ ∨ (∃ p : P, F = {p}) ∨ (∃ l : L, F = planeLineSet l) ∨ F = univ := by
  refine ⟨incidencePlaneMatroid_isFlat_cases, ?_⟩
  rintro (rfl | ⟨p, rfl⟩ | ⟨l, rfl⟩ | rfl)
  · exact Matroid.isFlat_iff_closure_eq.mpr incidencePlaneMatroid_closure_empty
  · exact (incidencePlanePointFlat (L := L) p).2
  · exact incidencePlaneMatroid_isFlat_line l
  · exact (incidencePlaneMatroid P L).ground_isFlat

noncomputable def incidencePlaneLineFlat (l : L) : MatroidFlat (incidencePlaneMatroid P L) :=
  ⟨planeLineSet l, incidencePlaneMatroid_isFlat_line l⟩

@[simp] theorem incidencePlaneLineFlat_val (l : L) :
    (incidencePlaneLineFlat (P := P) l).1 = planeLineSet l := rfl

theorem incidencePlaneLineFlat_rank (l : L) : MatroidFlat.rank (incidencePlaneLineFlat (P := P) l) = 2 := by
  obtain ⟨a, ha, b, hb, hab⟩ := planeLineSet_has_pair (P := P) l
  change matroidRank (incidencePlaneMatroid P L) (planeLineSet l) = 2
  rw [← incidencePlaneMatroid_closure_pair (l := l) hab ha hb, matroidRank_closure,
    matroidRank_indep (incidencePlaneMatroid_indep_pair a b), Set.ncard_pair hab]

theorem incidencePlaneLineFlat_injective :
    Function.Injective (incidencePlaneLineFlat (P := P) (L := L)) := by
  intro l m h
  exact planeLineSet_injective (congrArg Subtype.val h)

theorem incidencePlaneFlat_top_rank :
    MatroidFlat.rank (⊤ : MatroidFlat (incidencePlaneMatroid P L)) = 3 := incidencePlaneMatroid_rank

theorem incidencePlanePointFlat_le_lineFlat (p : P) (l : L) :
    incidencePlanePointFlat (L := L) p ≤ incidencePlaneLineFlat (P := P) l ↔ p ∈ l :=
  Set.singleton_subset_iff

end BooleanAntichainsKernel
