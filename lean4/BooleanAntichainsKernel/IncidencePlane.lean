import Mathlib.Combinatorics.Configuration
import Mathlib.Data.Set.Card

namespace BooleanAntichainsKernel

open Set
open scoped Classical

variable {P L : Type*} [Membership P L]

/-- The actual set of points incident with the line l. -/
def planeLineSet (l : L) : Set P := {p | p ∈ l}

@[simp] theorem mem_planeLineSet (p : P) (l : L) : p ∈ planeLineSet l ↔ p ∈ l := Iff.rfl

/-- Collinearity of the actual point set, with no coordinatization. -/
def PlaneCollinear (L : Type*) [Membership P L] (S : Set P) : Prop :=
  ∃ l : L, S ⊆ planeLineSet l

theorem PlaneCollinear.mono {S T : Set P} (hT : PlaneCollinear L T) (hST : S ⊆ T) :
    PlaneCollinear L S := by
  obtain ⟨l, hl⟩ := hT
  exact ⟨l, hST.trans hl⟩

variable [Configuration.ProjectivePlane P L]

theorem plane_line_eq_of_pair {a b : P} {l m : L} (hab : a ≠ b)
    (ha : a ∈ l) (hb : b ∈ l) (ha' : a ∈ m) (hb' : b ∈ m) : l = m :=
  (Configuration.Nondegenerate.eq_or_eq ha hb ha' hb').resolve_left hab

theorem plane_pair_collinear {a b : P} (hab : a ≠ b) : PlaneCollinear L ({a, b} : Set P) :=
  ⟨Configuration.HasLines.mkLine hab, by
    have h := Configuration.HasLines.mkLine_ax (P := P) (L := L) hab
    simpa only [Set.insert_subset_iff, Set.singleton_subset_iff, mem_planeLineSet] using h⟩

theorem planeLineSet_ne_univ (l : L) : planeLineSet l ≠ (univ : Set P) := by
  obtain ⟨p, hp⟩ := Configuration.Nondegenerate.exists_point (P := P) l
  intro h
  apply hp
  change p ∈ planeLineSet l
  rw [h]
  exact Set.mem_univ p

theorem planeLineSet_inter_of_ne {l m : L} (hlm : l ≠ m) :
    planeLineSet l ∩ planeLineSet m = {Configuration.HasPoints.mkPoint hlm} := by
  have hc := Configuration.HasPoints.mkPoint_ax (P := P) (L := L) hlm
  ext p
  constructor
  · intro hp
    exact Set.mem_singleton_iff.mpr
      ((Configuration.Nondegenerate.eq_or_eq (P := P) (L := L) hp.1 hc.1 hp.2 hc.2).resolve_right hlm)
  · rintro rfl
    exact hc

theorem plane_triple_noncollinear {a b c : P} {l : L} (hab : a ≠ b)
    (ha : a ∈ l) (hb : b ∈ l) (hc : c ∉ l) :
    ¬ PlaneCollinear L ({a, b, c} : Set P) := by
  rintro ⟨m, hm⟩
  have hm' : a ∈ m ∧ b ∈ m ∧ c ∈ m := by
    simpa only [Set.insert_subset_iff, Set.singleton_subset_iff, mem_planeLineSet] using hm
  have hlm := plane_line_eq_of_pair hab ha hb hm'.1 hm'.2.1
  exact hc (hlm.symm ▸ hm'.2.2)

variable [Fintype P] [Fintype L]

theorem planeLineSet_card (l : L) :
    (planeLineSet l).ncard = Configuration.ProjectivePlane.order P L + 1 :=
  Configuration.ProjectivePlane.pointCount_eq P l

theorem planeLineSet_has_pair (l : L) : ∃ a ∈ planeLineSet l, ∃ b ∈ planeLineSet l, a ≠ b := by
  apply (Set.one_lt_ncard (s := planeLineSet l)).mp
  rw [planeLineSet_card]
  have h := Configuration.ProjectivePlane.one_lt_order P L
  omega

theorem planeLineSet_injective : Function.Injective (planeLineSet (P := P) (L := L)) := by
  intro l m h
  obtain ⟨a, ha, b, hb, hab⟩ := planeLineSet_has_pair (P := P) l
  have ham : a ∈ planeLineSet m := h ▸ ha
  have hbm : b ∈ planeLineSet m := h ▸ hb
  exact plane_line_eq_of_pair hab ha hb ham hbm

theorem plane_exists_noncollinear_triple :
    ∃ a b c : P, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ ¬ PlaneCollinear L ({a, b, c} : Set P) := by
  obtain ⟨_p₁, _p₂, _p₃, l, _l₂, _l₃, _h⟩ :=
    Configuration.ProjectivePlane.exists_config (P := P) (L := L)
  obtain ⟨a, ha, b, hb, hab⟩ := planeLineSet_has_pair (P := P) l
  obtain ⟨c, hc⟩ := Configuration.Nondegenerate.exists_point (P := P) l
  exact ⟨a, b, c, hab, fun h ↦ hc (h ▸ ha), fun h ↦ hc (h ▸ hb),
    plane_triple_noncollinear hab ha hb hc⟩

theorem plane_card_points :
    Fintype.card P = Configuration.ProjectivePlane.order P L ^ 2 +
      Configuration.ProjectivePlane.order P L + 1 :=
  Configuration.ProjectivePlane.card_points P L

theorem plane_card_lines :
    Fintype.card L = Configuration.ProjectivePlane.order P L ^ 2 +
      Configuration.ProjectivePlane.order P L + 1 :=
  Configuration.ProjectivePlane.card_lines P L

end BooleanAntichainsKernel
