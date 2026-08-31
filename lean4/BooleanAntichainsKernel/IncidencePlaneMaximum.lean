import BooleanAntichainsKernel.IncidencePlaneFlatCounting
import BooleanAntichainsKernel.SimplifiedBasisCounts

namespace BooleanAntichainsKernel

open Finset
open scoped Classical

/-- The actual unordered three-point sets excluded from every incidence line. -/
abbrev PlaneNoncollinearTriple (P L : Type*) [Membership P L] :=
  {B : Finset P // B.card = 3 ∧ ¬ PlaneCollinear L (B : Set P)}

variable {P L : Type*} [Membership P L] [Configuration.ProjectivePlane P L] [Fintype P]

noncomputable instance : Fintype (PlaneNoncollinearTriple P L) := Subtype.fintype _

/-- Every nonloop parallel class is the original singleton point, as
follows from the already proved actual singleton and empty closures. -/
theorem incidencePlane_parallelClass_card_one (F : MatroidFlat (incidencePlaneMatroid P L))
    (hF : MatroidFlat.rank F = 1) : (parallelClassElements F).card = 1 := by
  obtain ⟨p, _hp, _hN, hcl⟩ := rank_one_flat_has_representative F hF
  have hval : F.1 = {p} := hcl.symm.trans (incidencePlaneMatroid_closure_singleton p)
  unfold parallelClassElements
  rw [← Set.ncard_eq_toFinset_card', hval, incidencePlaneMatroid_closure_empty,
    Set.sdiff_empty, Set.ncard_singleton]

variable [Fintype L]

/-- Consume the paper's maximum-antichain theorem and its actual
simplification fibres on the rank-three incidence-plane matroid. -/
theorem incidencePlane_maximum_count_bases :
    Fintype.card (BooleanAntichain 3 (MatroidFlat (incidencePlaneMatroid P L))) =
      Fintype.card (MatroidBases (incidencePlaneMatroid P L)) := by
  have h := maximumAntichain_count_eq_simplifiedBases (M := incidencePlaneMatroid P L)
  change Fintype.card
    (BooleanAntichain (MatroidFlat.rank (⊤ : MatroidFlat (incidencePlaneMatroid P L)))
      (MatroidFlat (incidencePlaneMatroid P L))) = _ at h
  rw [incidencePlaneFlat_top_rank] at h
  exact h.trans (simplifiedBasis_count_of_singleton_classes (incidencePlaneMatroid P L)
    incidencePlane_parallelClass_card_one)

/-- The map leaves the finite point set unchanged in both directions. -/
noncomputable def incidencePlaneBasesEquivTriples :
    MatroidBases (incidencePlaneMatroid P L) ≃ PlaneNoncollinearTriple P L where
  toFun B := ⟨B.1, by
    simpa only [Set.ncard_coe_finset] using
      (incidencePlaneMatroid_isBase_iff (B.1 : Set P)).mp B.2⟩
  invFun B := ⟨B.1, (incidencePlaneMatroid_isBase_iff (B.1 : Set P)).mpr (by
    simpa only [Set.ncard_coe_finset] using B.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem incidencePlaneBasesEquivTriples_val (B : MatroidBases (incidencePlaneMatroid P L)) :
    (incidencePlaneBasesEquivTriples B).1 = B.1 := rfl

theorem incidencePlane_three_count_noncollinear :
    Fintype.card (BooleanAntichain 3 (MatroidFlat (incidencePlaneMatroid P L))) =
      Fintype.card (PlaneNoncollinearTriple P L) := by
  rw [incidencePlane_maximum_count_bases,
    Fintype.card_congr (incidencePlaneBasesEquivTriples (P := P) (L := L))]

theorem incidencePlane_count_above_three (k : ℕ) (hk : 3 < k) :
    Fintype.card (BooleanAntichain k (MatroidFlat (incidencePlaneMatroid P L))) = 0 := by
  apply Fintype.card_eq_zero_iff.mpr
  refine ⟨fun C ↦ ?_⟩
  have hH := (isBooleanTuple_iff_antichain_of_equiv C.1 (canonicalEnumeration C)).mpr C.2.2
  have h := (boolean_face_rank_bounds hH MatroidFlat.rank MatroidFlat.rank_strictMono Finset.univ).1
  simp only [meetFace_univ, Finset.card_univ, Fintype.card_fin, incidencePlaneFlat_top_rank] at h
  omega

end BooleanAntichainsKernel
