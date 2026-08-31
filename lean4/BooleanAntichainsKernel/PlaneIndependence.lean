import BooleanAntichainsKernel.IncidencePlane

namespace BooleanAntichainsKernel

open Set
open scoped Classical

variable {P L : Type*} [Membership P L]

/-- The literal independent point sets of a rank-three projective plane:
at most three points, with every three-point independent set noncollinear. -/
def PlaneIndependent (L : Type*) [Membership P L] (I : Set P) : Prop :=
  I.ncard ≤ 3 ∧ (I.ncard = 3 → ¬ PlaneCollinear L I)

theorem planeIndependent_of_card_le_two {I : Set P} (hI : I.ncard ≤ 2) :
    PlaneIndependent L I := by
  refine ⟨by omega, ?_⟩
  intro h
  omega

theorem planeIndependent_empty : PlaneIndependent L (∅ : Set P) :=
  planeIndependent_of_card_le_two (by simp)

variable [Fintype P]

theorem PlaneIndependent.mono {I J : Set P} (hJ : PlaneIndependent L J) (hIJ : I ⊆ J) :
    PlaneIndependent L I := by
  have hcard := Set.ncard_le_ncard hIJ
  have hJcard := hJ.1
  refine ⟨hcard.trans hJ.1, ?_⟩
  intro hI3 hcol
  have hJ3 : J.ncard = 3 := by omega
  have hEq : I = J := Set.eq_of_subset_of_ncard_le hIJ (by omega)
  exact hJ.2 hJ3 (hEq ▸ hcol)

variable [Configuration.ProjectivePlane P L]

omit [Fintype P] in
theorem plane_collinear_of_ncard_two {I : Set P} (hI : I.ncard = 2) : PlaneCollinear L I := by
  obtain ⟨a, b, hab, rfl⟩ := Set.ncard_eq_two.mp hI
  exact plane_pair_collinear hab

omit [Fintype P] in
theorem plane_line_eq_of_subset_card_two {I : Set P} {l m : L} (hI : I.ncard = 2)
    (hl : I ⊆ planeLineSet l) (hm : I ⊆ planeLineSet m) : l = m := by
  obtain ⟨a, b, hab, rfl⟩ := Set.ncard_eq_two.mp hI
  exact plane_line_eq_of_pair hab (hl (by simp)) (hl (by simp))
    (hm (by simp)) (hm (by simp))

omit [Fintype P] in
theorem plane_noncollinear_insert_of_line_pair {I : Set P} {l : L} {e : P}
    (hI : I.ncard = 2) (hl : I ⊆ planeLineSet l) (he : e ∉ l) :
    ¬ PlaneCollinear L (insert e I) := by
  rintro ⟨m, hm⟩
  have hlm := plane_line_eq_of_subset_card_two hI hl ((Set.subset_insert e I).trans hm)
  have hem : e ∈ m := hm (Set.mem_insert e I)
  exact he (hlm.symm ▸ hem)

/-- The finite matroid augmentation axiom follows from unique lines
through pairs and a point of the larger independent set off that line. -/
theorem planeIndependent_augment {I J : Set P} (_hI : PlaneIndependent L I)
    (hJ : PlaneIndependent L J) (hIJ : I.ncard < J.ncard) :
    ∃ e ∈ J, e ∉ I ∧ PlaneIndependent L (insert e I) := by
  have hJcard := hJ.1
  by_cases hsmall : I.ncard ≤ 1
  · have hnot : ¬ J ⊆ I := fun h ↦ hIJ.not_ge (Set.ncard_le_ncard h)
    obtain ⟨e, heJ, heI⟩ := Set.not_subset.mp hnot
    refine ⟨e, heJ, heI, planeIndependent_of_card_le_two ?_⟩
    rw [Set.ncard_insert_of_notMem heI]
    omega
  · have hI2 : I.ncard = 2 := by omega
    have hJ3 : J.ncard = 3 := by omega
    obtain ⟨l, hl⟩ := plane_collinear_of_ncard_two (L := L) hI2
    have hnot : ¬ J ⊆ planeLineSet l := fun h ↦ hJ.2 hJ3 ⟨l, h⟩
    obtain ⟨e, heJ, heLine⟩ := Set.not_subset.mp hnot
    have heI : e ∉ I := fun h ↦ heLine (hl h)
    have hins : (insert e I).ncard = 3 := by rw [Set.ncard_insert_of_notMem heI, hI2]
    exact ⟨e, heJ, heI, hins.le,
      fun _ ↦ plane_noncollinear_insert_of_line_pair hI2 hl heLine⟩

end BooleanAntichainsKernel
