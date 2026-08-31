import BooleanAntichainsKernel.IncidencePlaneJoins

namespace BooleanAntichainsKernel

open scoped Classical

/-- Actual ordered distinct lines, with no quotient by their transposition. -/
abbrev PlaneDistinctLines (L : Type*) := Σ l : L, {m : L // m ≠ l}

/-- An actual line and a point outside it. -/
abbrev PlaneNonincidentFlag (P L : Type*) [Membership P L] := Σ l : L, {p : P // p ∉ l}

abbrev PlaneJoinPairData (P L : Type*) [Membership P L] :=
  PlaneDistinctLines L ⊕ PlaneNonincidentFlag P L ⊕ PlaneNonincidentFlag P L

variable {P L : Type*} [Membership P L] [Configuration.ProjectivePlane P L]
variable [Fintype P] [Fintype L]

noncomputable def planeDistinctLinesPair (x : PlaneDistinctLines L) :
    ProperTopJoinPair (L := MatroidFlat (incidencePlaneMatroid P L)) :=
  ⟨(incidencePlaneLineFlat x.1, incidencePlaneLineFlat x.2.1),
    incidencePlaneLineFlat_ne_top x.1, incidencePlaneLineFlat_ne_top x.2.1,
    (incidencePlane_line_sup_line_eq_top_iff x.1 x.2.1).mpr x.2.2.symm⟩

noncomputable def planeNonincidentPointLine (x : PlaneNonincidentFlag P L) :
    ProperTopJoinPair (L := MatroidFlat (incidencePlaneMatroid P L)) :=
  ⟨(incidencePlanePointFlat x.2.1, incidencePlaneLineFlat x.1),
    incidencePlanePointFlat_ne_top x.2.1, incidencePlaneLineFlat_ne_top x.1,
    (incidencePlane_point_sup_line_eq_top_iff x.2.1 x.1).mpr x.2.2⟩

noncomputable def planeNonincidentLinePoint (x : PlaneNonincidentFlag P L) :
    ProperTopJoinPair (L := MatroidFlat (incidencePlaneMatroid P L)) :=
  ⟨(incidencePlaneLineFlat x.1, incidencePlanePointFlat x.2.1),
    incidencePlaneLineFlat_ne_top x.1, incidencePlanePointFlat_ne_top x.2.1,
    (incidencePlane_line_sup_point_eq_top_iff x.1 x.2.1).mpr x.2.2⟩

theorem planeDistinctLinesPair_injective :
    Function.Injective (planeDistinctLinesPair (P := P) (L := L)) := by
  rintro ⟨l, ⟨m, hm⟩⟩ ⟨n, ⟨t, ht⟩⟩ h
  have hl : l = n := incidencePlaneLineFlat_injective
    (congrArg (fun z : ProperTopJoinPair (L := MatroidFlat (incidencePlaneMatroid P L)) ↦ z.1.1) h)
  have hm' : m = t := incidencePlaneLineFlat_injective
    (congrArg (fun z : ProperTopJoinPair (L := MatroidFlat (incidencePlaneMatroid P L)) ↦ z.1.2) h)
  subst n
  subst t
  rfl

theorem planeNonincidentPointLine_injective :
    Function.Injective (planeNonincidentPointLine (P := P) (L := L)) := by
  rintro ⟨l, ⟨p, hp⟩⟩ ⟨m, ⟨q, hq⟩⟩ h
  have hl : l = m := incidencePlaneLineFlat_injective
    (congrArg (fun z : ProperTopJoinPair (L := MatroidFlat (incidencePlaneMatroid P L)) ↦ z.1.2) h)
  have hp' : p = q := incidencePlanePointFlat_injective
    (congrArg (fun z : ProperTopJoinPair (L := MatroidFlat (incidencePlaneMatroid P L)) ↦ z.1.1) h)
  subst m
  subst q
  rfl

theorem planeNonincidentLinePoint_injective :
    Function.Injective (planeNonincidentLinePoint (P := P) (L := L)) := by
  rintro ⟨l, ⟨p, hp⟩⟩ ⟨m, ⟨q, hq⟩⟩ h
  have hl : l = m := incidencePlaneLineFlat_injective
    (congrArg (fun z : ProperTopJoinPair (L := MatroidFlat (incidencePlaneMatroid P L)) ↦ z.1.1) h)
  have hp' : p = q := incidencePlanePointFlat_injective
    (congrArg (fun z : ProperTopJoinPair (L := MatroidFlat (incidencePlaneMatroid P L)) ↦ z.1.2) h)
  subst m
  subst q
  rfl

/-- Both orientations of the nonincident point-line pair are retained. -/
noncomputable def planeJoinPairDataToPair :
    PlaneJoinPairData P L → ProperTopJoinPair (L := MatroidFlat (incidencePlaneMatroid P L))
  | Sum.inl x => planeDistinctLinesPair x
  | Sum.inr (Sum.inl x) => planeNonincidentPointLine x
  | Sum.inr (Sum.inr x) => planeNonincidentLinePoint x

theorem planeJoinPairDataToPair_injective :
    Function.Injective (planeJoinPairDataToPair (P := P) (L := L)) := by
  intro x y h
  have hfst := congrArg (fun z : ProperTopJoinPair (L := MatroidFlat (incidencePlaneMatroid P L)) ↦
    MatroidFlat.rank z.1.1) h
  have hsnd := congrArg (fun z : ProperTopJoinPair (L := MatroidFlat (incidencePlaneMatroid P L)) ↦
    MatroidFlat.rank z.1.2) h
  rcases x with x | x | x <;> rcases y with y | y | y
  all_goals simp only [planeJoinPairDataToPair, planeDistinctLinesPair, planeNonincidentPointLine,
    planeNonincidentLinePoint, incidencePlanePointFlat_rank, incidencePlaneLineFlat_rank] at hfst hsnd
  all_goals try omega
  all_goals first
    | exact congrArg Sum.inl (planeDistinctLinesPair_injective h)
    | exact congrArg (fun x ↦ Sum.inr (Sum.inl x)) (planeNonincidentPointLine_injective h)
    | exact congrArg (fun x ↦ Sum.inr (Sum.inr x)) (planeNonincidentLinePoint_injective h)

end BooleanAntichainsKernel
