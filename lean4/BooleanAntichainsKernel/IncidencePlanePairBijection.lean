import BooleanAntichainsKernel.IncidencePlanePairData

namespace BooleanAntichainsKernel

open scoped Classical

variable {P L : Type*} [Membership P L] [Configuration.ProjectivePlane P L]
variable [Fintype P] [Fintype L]

/-- Exhaust the actual flat classification. Bottom and top entries are
excluded; point-point pairs cannot join to top; the remaining cases are
exactly line-line and the two nonincident point-line orientations. -/
theorem planeJoinPairDataToPair_surjective :
    Function.Surjective (planeJoinPairDataToPair (P := P) (L := L)) := by
  rintro ⟨⟨F, G⟩, hF, hG, hFG⟩
  obtain ⟨a, rfl⟩ := incidencePlaneFlatOfCode_surjective F
  obtain ⟨b, rfl⟩ := incidencePlaneFlatOfCode_surjective G
  rcases a with ⟨⟩ | p | l | ⟨⟩ <;> rcases b with ⟨⟩ | q | m | ⟨⟩
  all_goals simp [incidencePlaneFlatOfCode] at hF hG hFG
  · exact ⟨Sum.inr (Sum.inl ⟨m, ⟨p, hFG⟩⟩), rfl⟩
  · exact ⟨Sum.inr (Sum.inr ⟨l, ⟨q, hFG⟩⟩), rfl⟩
  · exact ⟨Sum.inl ⟨l, ⟨m, fun hml ↦ hFG hml.symm⟩⟩, rfl⟩

noncomputable def planeJoinPairEquiv :
    PlaneJoinPairData P L ≃ ProperTopJoinPair (L := MatroidFlat (incidencePlaneMatroid P L)) :=
  Equiv.ofBijective planeJoinPairDataToPair
    ⟨planeJoinPairDataToPair_injective, planeJoinPairDataToPair_surjective⟩

theorem planeJoinPairEquiv_line_line (x : PlaneDistinctLines L) :
    (planeJoinPairEquiv (P := P) (Sum.inl x)).1 =
      (incidencePlaneLineFlat x.1, incidencePlaneLineFlat x.2.1) := rfl

theorem planeJoinPairEquiv_point_line (x : PlaneNonincidentFlag P L) :
    (planeJoinPairEquiv (Sum.inr (Sum.inl x))).1 =
      (incidencePlanePointFlat x.2.1, incidencePlaneLineFlat x.1) := rfl

theorem planeJoinPairEquiv_line_point (x : PlaneNonincidentFlag P L) :
    (planeJoinPairEquiv (Sum.inr (Sum.inr x))).1 =
      (incidencePlaneLineFlat x.1, incidencePlanePointFlat x.2.1) := rfl

end BooleanAntichainsKernel
