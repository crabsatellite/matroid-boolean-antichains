import BooleanAntichainsKernel.PlaneIndependence
import BooleanAntichainsKernel.MatroidRank
import Mathlib.Combinatorics.Matroid.IndepAxioms

namespace BooleanAntichainsKernel

open Set
open scoped Classical

variable (P L : Type*) [Membership P L] [Configuration.ProjectivePlane P L] [Fintype P]

/-- The actual simple rank-three matroid of the incidence plane. Its
independence axioms are derived from the incidence relation above. -/
noncomputable def incidencePlaneMatroid : Matroid P :=
  (IndepMatroid.ofFinite (Set.toFinite (univ : Set P)) (PlaneIndependent L)
    planeIndependent_empty (fun {_I _J} hJ hIJ ↦ hJ.mono hIJ)
    (fun {_I _J} hI hJ hIJ ↦ planeIndependent_augment hI hJ hIJ)
    (fun {_I} _ ↦ Set.subset_univ _)).matroid

@[simp] theorem incidencePlaneMatroid_ground : (incidencePlaneMatroid P L).E = univ := rfl

@[simp] theorem incidencePlaneMatroid_indep_iff (I : Set P) :
    (incidencePlaneMatroid P L).Indep I ↔
      I.ncard ≤ 3 ∧ (I.ncard = 3 → ¬ PlaneCollinear L I) := Iff.rfl

variable {P L}

theorem incidencePlaneMatroid_indep_of_card_le_two {I : Set P} (hI : I.ncard ≤ 2) :
    (incidencePlaneMatroid P L).Indep I :=
  planeIndependent_of_card_le_two hI

theorem incidencePlaneMatroid_indep_singleton (p : P) :
    (incidencePlaneMatroid P L).Indep {p} :=
  incidencePlaneMatroid_indep_of_card_le_two (by simp)

theorem incidencePlaneMatroid_indep_pair (p q : P) :
    (incidencePlaneMatroid P L).Indep {p, q} :=
  incidencePlaneMatroid_indep_of_card_le_two (by
    simpa only [Set.ncard_singleton] using Set.ncard_insert_le p ({q} : Set P))

theorem incidencePlaneMatroid_isBase_of_card_three {B : Set P}
    (hB : (incidencePlaneMatroid P L).Indep B) (hcard : B.ncard = 3) :
    (incidencePlaneMatroid P L).IsBase B := by
  apply hB.isBase_of_maximal
  intro J hJ hBJ
  apply Set.eq_of_subset_of_ncard_le hBJ
  rw [hcard]
  exact ((incidencePlaneMatroid_indep_iff P L J).mp hJ).1

variable [Fintype L]

theorem incidencePlaneMatroid_exists_base_three :
    ∃ B : Set P, (incidencePlaneMatroid P L).IsBase B ∧ B.ncard = 3 := by
  obtain ⟨a, b, c, hab, hac, hbc, hnc⟩ := plane_exists_noncollinear_triple (P := P) (L := L)
  have hcard : ({a, b, c} : Set P).ncard = 3 := by
    rw [Set.ncard_insert_of_notMem (by simp [hab, hac]), Set.ncard_pair hbc]
  have hI : (incidencePlaneMatroid P L).Indep ({a, b, c} : Set P) :=
    ⟨hcard.le, fun _ ↦ hnc⟩
  exact ⟨{a, b, c}, incidencePlaneMatroid_isBase_of_card_three hI hcard, hcard⟩

theorem incidencePlaneMatroid_rank :
    matroidRank (incidencePlaneMatroid P L) (incidencePlaneMatroid P L).E = 3 := by
  obtain ⟨B, hB, hcard⟩ := incidencePlaneMatroid_exists_base_three (P := P) (L := L)
  rw [← hB.closure_eq, matroidRank_closure, matroidRank_indep hB.indep, hcard]

/-- The bases in the manuscript's maximum-layer argument are exactly
the actual three-element noncollinear subsets of plane points. -/
theorem incidencePlaneMatroid_isBase_iff (B : Set P) :
    (incidencePlaneMatroid P L).IsBase B ↔ B.ncard = 3 ∧ ¬ PlaneCollinear L B := by
  constructor
  · intro hB
    have hcard : B.ncard = 3 := by
      rw [← matroidRank_indep hB.indep, ← matroidRank_closure (incidencePlaneMatroid P L) B,
        hB.closure_eq]
      exact incidencePlaneMatroid_rank
    exact ⟨hcard, ((incidencePlaneMatroid_indep_iff P L B).mp hB.indep).2 hcard⟩
  · rintro ⟨hcard, hnc⟩
    exact incidencePlaneMatroid_isBase_of_card_three ⟨hcard.le, fun _ ↦ hnc⟩ hcard

end BooleanAntichainsKernel
