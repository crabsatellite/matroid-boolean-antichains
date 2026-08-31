import BooleanAntichainsKernel.IncidencePlaneMatroid

namespace BooleanAntichainsKernel

open Set
open scoped Classical

variable {P L : Type*} [Membership P L] [Configuration.ProjectivePlane P L] [Fintype P]

theorem incidencePlaneMatroid_closure_of_card_le_one (I : Set P) (hcard : I.ncard ≤ 1) :
    (incidencePlaneMatroid P L).closure I = I := by
  have hI := incidencePlaneMatroid_indep_of_card_le_two (L := L) (I := I) (by omega)
  apply Set.Subset.antisymm ?_ ((incidencePlaneMatroid P L).subset_closure I (by simp))
  intro e he
  by_contra heI
  have hi : (incidencePlaneMatroid P L).Indep (insert e I) := by
    apply incidencePlaneMatroid_indep_of_card_le_two
    rw [Set.ncard_insert_of_notMem heI]
    omega
  exact ((hI.notMem_closure_iff_of_notMem heI (by simp)).mpr hi) he

@[simp] theorem incidencePlaneMatroid_closure_empty :
    (incidencePlaneMatroid P L).closure ∅ = ∅ :=
  incidencePlaneMatroid_closure_of_card_le_one ∅ (by simp)

@[simp] theorem incidencePlaneMatroid_closure_singleton (p : P) :
    (incidencePlaneMatroid P L).closure {p} = {p} :=
  incidencePlaneMatroid_closure_of_card_le_one {p} (by simp)

/-- The closure of two distinct plane points is their unique actual
incidence line, proved using the matroid's independent-set closure rule. -/
theorem incidencePlaneMatroid_closure_pair {a b : P} {l : L} (hab : a ≠ b)
    (ha : a ∈ l) (hb : b ∈ l) :
    (incidencePlaneMatroid P L).closure {a, b} = planeLineSet l := by
  have hI := incidencePlaneMatroid_indep_pair (L := L) a b
  have hIL : ({a, b} : Set P) ⊆ planeLineSet l := by
    simpa only [Set.insert_subset_iff, Set.singleton_subset_iff, mem_planeLineSet] using And.intro ha hb
  apply Set.Subset.antisymm
  · intro e he
    by_contra heLine
    have heI : e ∉ ({a, b} : Set P) := fun h ↦ heLine (hIL h)
    have hc : (insert e ({a, b} : Set P)).ncard = 3 := by
      rw [Set.ncard_insert_of_notMem heI, Set.ncard_pair hab]
    have hi : (incidencePlaneMatroid P L).Indep (insert e ({a, b} : Set P)) :=
      ⟨hc.le, fun _ ↦ plane_noncollinear_insert_of_line_pair (Set.ncard_pair hab) hIL heLine⟩
    exact ((hI.notMem_closure_iff_of_notMem heI (by simp)).mpr hi) he
  · intro e he
    rw [hI.mem_closure_iff']
    refine ⟨by simp, ?_⟩
    intro hi
    by_contra heI
    have hc : (insert e ({a, b} : Set P)).ncard = 3 := by
      rw [Set.ncard_insert_of_notMem heI, Set.ncard_pair hab]
    exact ((incidencePlaneMatroid_indep_iff P L _).mp hi).2 hc
      ⟨l, Set.insert_subset he hIL⟩

theorem incidencePlaneMatroid_closure_three {B : Set P}
    (hB : (incidencePlaneMatroid P L).Indep B) (hcard : B.ncard = 3) :
    (incidencePlaneMatroid P L).closure B = univ :=
  (incidencePlaneMatroid_isBase_of_card_three hB hcard).closure_eq

end BooleanAntichainsKernel
