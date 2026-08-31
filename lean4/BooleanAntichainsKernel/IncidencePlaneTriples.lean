import BooleanAntichainsKernel.IncidencePlaneMaximum
import Mathlib.Data.Finset.Powerset

namespace BooleanAntichainsKernel

open Finset
open scoped Classical

abbrev PlaneCollinearTriple (P L : Type*) [Membership P L] :=
  {B : Finset P // B.card = 3 ∧ PlaneCollinear L (B : Set P)}

variable {P L : Type*} [Membership P L] [Configuration.ProjectivePlane P L] [Fintype P]

abbrev PlaneLineTriple (l : L) :=
  {B : Finset P // B ⊆ (planeLineSet l).toFinset ∧ B.card = 3}

noncomputable instance : Fintype (PlaneCollinearTriple P L) := Subtype.fintype _
noncomputable instance (l : L) : Fintype (PlaneLineTriple (P := P) l) := Subtype.fintype _

omit [Configuration.ProjectivePlane P L] in
theorem planeLineTriple_subset {l : L} (B : PlaneLineTriple (P := P) l) :
    (B.1 : Set P) ⊆ planeLineSet l := fun _ hp ↦ Set.mem_toFinset.mp (B.2.1 hp)

omit [Fintype P] in
theorem plane_triple_line_unique {B : Finset P} (hB : B.card = 3) {l m : L}
    (hl : (B : Set P) ⊆ planeLineSet l) (hm : (B : Set P) ⊆ planeLineSet m) : l = m := by
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (show 1 < B.card by omega)
  exact plane_line_eq_of_pair (l := l) (m := m) hab (hl ha) (hl hb) (hm ha) (hm hb)

noncomputable def planeLineTripleForget (x : Σ l : L, PlaneLineTriple (P := P) l) :
    PlaneCollinearTriple P L := ⟨x.2.1, x.2.2.2, ⟨x.1, planeLineTriple_subset x.2⟩⟩

theorem planeLineTripleForget_injective :
    Function.Injective (planeLineTripleForget (P := P) (L := L)) := by
  rintro ⟨l, B⟩ ⟨m, C⟩ h
  have hBC : B.1 = C.1 := congrArg Subtype.val h
  have hlm : l = m := plane_triple_line_unique B.2.2 (planeLineTriple_subset B)
    (by rw [hBC]; exact planeLineTriple_subset C)
  subst m
  have hEq : B = C := Subtype.ext hBC
  subst C
  rfl

omit [Configuration.ProjectivePlane P L] in
theorem planeLineTripleForget_surjective :
    Function.Surjective (planeLineTripleForget (P := P) (L := L)) := by
  intro B
  obtain ⟨l, hl⟩ := B.2.2
  exact ⟨⟨l, ⟨B.1, fun p hp ↦ Set.mem_toFinset.mpr (hl hp), B.2.1⟩⟩, rfl⟩

/-- A collinear unordered triple lies on one and only one actual line. -/
noncomputable def planeLineTripleEquiv :
    (Σ l : L, PlaneLineTriple (P := P) l) ≃ PlaneCollinearTriple P L :=
  Equiv.ofBijective planeLineTripleForget
    ⟨planeLineTripleForget_injective, planeLineTripleForget_surjective⟩

omit [Configuration.ProjectivePlane P L] in
theorem planeTriple_partition_card :
    Fintype.card (PlaneCollinearTriple P L) + Fintype.card (PlaneNoncollinearTriple P L) =
      (Fintype.card P).choose 3 := by
  have hc : Fintype.card (PlaneCollinearTriple P L) =
      (((univ : Finset P).powersetCard 3).filter
        (fun B : Finset P ↦ PlaneCollinear L (B : Set P))).card :=
    Fintype.card_of_subtype _ (fun B ↦ by
      simp only [mem_filter, mem_powersetCard, subset_univ, true_and])
  have hn : Fintype.card (PlaneNoncollinearTriple P L) =
      (((univ : Finset P).powersetCard 3).filter
        (fun B : Finset P ↦ ¬ PlaneCollinear L (B : Set P))).card :=
    Fintype.card_of_subtype _ (fun B ↦ by
      simp only [mem_filter, mem_powersetCard, subset_univ, true_and])
  rw [hc, hn, Finset.card_filter_add_card_filter_not, Finset.card_powersetCard, card_univ]

variable [Fintype L]

theorem planeLineTriple_card (l : L) :
    Fintype.card (PlaneLineTriple (P := P) l) =
      (Configuration.ProjectivePlane.order P L + 1).choose 3 := by
  rw [Fintype.card_of_subtype ((planeLineSet l).toFinset.powersetCard 3)
      (fun B ↦ by simp only [mem_powersetCard]),
    Finset.card_powersetCard, ← Set.ncard_eq_toFinset_card', planeLineSet_card]

theorem plane_collinearTriple_count :
    Fintype.card (PlaneCollinearTriple P L) =
      Fintype.card L * (Configuration.ProjectivePlane.order P L + 1).choose 3 := by
  rw [← Fintype.card_congr (planeLineTripleEquiv (P := P) (L := L)), Fintype.card_sigma]
  simp only [planeLineTriple_card, Finset.sum_const, card_univ, smul_eq_mul]

/-- The subtraction is earned from a partition of all actual triples. -/
theorem plane_noncollinearTriple_count :
    Fintype.card (PlaneNoncollinearTriple P L) =
      (Fintype.card P).choose 3 -
        Fintype.card L * (Configuration.ProjectivePlane.order P L + 1).choose 3 := by
  have h := planeTriple_partition_card (P := P) (L := L)
  rw [plane_collinearTriple_count] at h
  omega

theorem incidencePlane_three_count :
    Fintype.card (BooleanAntichain 3 (MatroidFlat (incidencePlaneMatroid P L))) =
      (Configuration.ProjectivePlane.order P L ^ 2 + Configuration.ProjectivePlane.order P L + 1).choose 3 -
        (Configuration.ProjectivePlane.order P L ^ 2 + Configuration.ProjectivePlane.order P L + 1) *
          (Configuration.ProjectivePlane.order P L + 1).choose 3 := by
  rw [incidencePlane_three_count_noncollinear, plane_noncollinearTriple_count,
    plane_card_points (L := L), plane_card_lines (P := P)]

end BooleanAntichainsKernel
