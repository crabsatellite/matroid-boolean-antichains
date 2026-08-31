import BooleanAntichainsKernel.LatticeTransport
import Mathlib.Order.LatticeIntervals

/-! Literal inclusion and lifting of Boolean antichains in `[X, top]`.
The common meet, including the empty-family top, is preserved by inclusion. -/

namespace BooleanAntichainsKernel

open Set Finset
open scoped Classical

variable {L : Type*} [Lattice L] [OrderTop L] (X : L)

local instance : Fact (X ≤ (⊤ : L)) := ⟨le_top⟩

lemma upperInterval_val_inf {ι : Type*} (S : Finset ι) (f : ι → Set.Icc X (⊤ : L)) :
    (S.inf f).1 = S.inf (fun i ↦ (f i).1) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    rw [Finset.inf_insert, Finset.inf_insert]
    change (f i).1 ⊓ (S.inf f).1 = _
    rw [ih]

lemma upperInterval_val_meetFace {k : ℕ} (H : Fin k → Set.Icc X (⊤ : L)) (S : Finset (Fin k)) :
    (meetFace H S).1 = meetFace (fun i ↦ (H i).1) S :=
  upperInterval_val_inf X _ H

lemma upperInterval_booleanTuple_iff {k : ℕ} (H : Fin k → Set.Icc X (⊤ : L)) :
    IsBooleanTuple (fun i ↦ (H i).1) ↔ IsBooleanTuple H := by
  constructor
  · intro h
    constructor
    · intro S T hST
      apply h.1
      simpa only [upperInterval_val_meetFace] using congrArg Subtype.val hST
    · intro S T
      apply Subtype.ext
      change (meetFace H (S ∪ T)).1 = (meetFace H S).1 ⊔ (meetFace H T).1
      simp only [upperInterval_val_meetFace]
      exact h.2 S T
  · intro h
    constructor
    · intro S T hST
      apply h.1
      apply Subtype.ext
      simpa only [upperInterval_val_meetFace] using hST
    · intro S T
      have hj := congrArg Subtype.val (h.2 S T)
      simpa only [upperInterval_val_meetFace, Set.Icc.coe_sup] using hj

variable [DecidableEq L]

def forgetUpperIntervalFamily (D : Finset (Set.Icc X (⊤ : L))) : Finset L := D.image Subtype.val

lemma forgetUpperIntervalFamily_card (D : Finset (Set.Icc X (⊤ : L))) :
    (forgetUpperIntervalFamily X D).card = D.card :=
  Finset.card_image_of_injective D Subtype.val_injective

lemma forgetUpperIntervalFamily_inf (D : Finset (Set.Icc X (⊤ : L))) :
    (forgetUpperIntervalFamily X D).inf id = (D.inf id).1 := by
  rw [forgetUpperIntervalFamily, Finset.inf_image]
  exact (upperInterval_val_inf X D id).symm

lemma forgetUpperIntervalFamily_boolean_iff (D : Finset (Set.Icc X (⊤ : L))) :
    IsBooleanAntichain (forgetUpperIntervalFamily X D) ↔ IsBooleanAntichain D := by
  let e : Fin D.card ≃ D := (Finset.equivFin D).symm
  let H : Fin D.card → Set.Icc X (⊤ : L) := fun i ↦ (e i).1
  let V : Fin D.card → L := fun i ↦ (H i).1
  have hHinj : Function.Injective H := Subtype.val_injective.comp e.injective
  have hVinj : Function.Injective V := Subtype.val_injective.comp hHinj
  have hcarrier : orderedCarrier H = D := orderedCarrier_of_equiv D e
  have hVcarrier : orderedCarrier V = forgetUpperIntervalFamily X D := by
    calc
      _ = (orderedCarrier H).image Subtype.val := by
        simp only [orderedCarrier, Finset.image_image]
        rfl
      _ = forgetUpperIntervalFamily X D := congrArg (fun S ↦ S.image Subtype.val) hcarrier
  have hV : IsBooleanTuple V ↔ IsBooleanAntichain (orderedCarrier V) :=
    isBooleanTuple_iff_antichain_of_equiv (orderedCarrier V) (indexEquivCarrier V hVinj)
  have hH : IsBooleanTuple H ↔ IsBooleanAntichain D :=
    isBooleanTuple_iff_antichain_of_equiv D e
  exact ((hV.trans (Iff.of_eq (congrArg IsBooleanAntichain hVcarrier))).symm.trans
    (upperInterval_booleanTuple_iff X H)).trans hH

variable [Fintype (Set.Icc X (⊤ : L))]

noncomputable def liftUpperIntervalFamily (C : Finset L) : Finset (Set.Icc X (⊤ : L)) :=
  Finset.univ.filter fun F ↦ F.1 ∈ C

lemma forget_liftUpperIntervalFamily (C : Finset L) (hC : ∀ a ∈ C, X ≤ a) :
    forgetUpperIntervalFamily X (liftUpperIntervalFamily X C) = C := by
  ext a
  constructor
  · intro ha
    rcases Finset.mem_image.mp ha with ⟨F, hF, rfl⟩
    exact (Finset.mem_filter.mp hF).2
  · intro ha
    exact Finset.mem_image.mpr ⟨⟨a, hC a ha, le_top⟩,
      Finset.mem_filter.mpr ⟨mem_univ _, ha⟩, rfl⟩

lemma lift_forgetUpperIntervalFamily (D : Finset (Set.Icc X (⊤ : L))) :
    liftUpperIntervalFamily X (forgetUpperIntervalFamily X D) = D := by
  ext F
  simp only [liftUpperIntervalFamily, forgetUpperIntervalFamily, Finset.mem_filter,
    Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · rintro ⟨G, hG, hGF⟩
    exact (Subtype.ext hGF : G = F) ▸ hG
  · intro hF
    exact ⟨F, hF, rfl⟩

variable [OrderBot L]

def forgetUpperIntervalAntichain {k : ℕ} (D : BooleanAntichain k (Set.Icc X (⊤ : L))) :
    BooleanAntichain k L :=
  ⟨forgetUpperIntervalFamily X D.1, (forgetUpperIntervalFamily_card X D.1).trans D.2.1,
    (forgetUpperIntervalFamily_boolean_iff X D.1).mpr D.2.2⟩

noncomputable def liftUpperIntervalAntichain {k : ℕ} (C : BooleanAntichain k L)
    (hC : X ≤ C.1.inf id) : BooleanAntichain k (Set.Icc X (⊤ : L)) := by
  have hmem : ∀ a ∈ C.1, X ≤ a := fun a ha ↦ hC.trans (Finset.inf_le ha)
  have hforget := forget_liftUpperIntervalFamily X C.1 hmem
  refine ⟨liftUpperIntervalFamily X C.1, ?_, ?_⟩
  · rw [← forgetUpperIntervalFamily_card, hforget]
    exact C.2.1
  · apply (forgetUpperIntervalFamily_boolean_iff X _).mp
    rw [hforget]
    exact C.2.2

omit [Fintype (Set.Icc X (⊤ : L))] in
lemma forgetUpperIntervalAntichain_lower {k : ℕ} (D : BooleanAntichain k (Set.Icc X (⊤ : L))) :
    X ≤ (forgetUpperIntervalAntichain X D).1.inf id := by
  rw [show (forgetUpperIntervalAntichain X D).1 = forgetUpperIntervalFamily X D.1 from rfl,
    forgetUpperIntervalFamily_inf]
  exact (D.1.inf id).2.1

lemma forget_liftUpperIntervalAntichain {k : ℕ} (C : BooleanAntichain k L)
    (hC : X ≤ C.1.inf id) :
    forgetUpperIntervalAntichain X (liftUpperIntervalAntichain X C hC) = C := by
  apply Subtype.ext
  exact forget_liftUpperIntervalFamily X C.1 (fun a ha ↦ hC.trans (Finset.inf_le ha))

lemma lift_forgetUpperIntervalAntichain {k : ℕ} (D : BooleanAntichain k (Set.Icc X (⊤ : L)))
    (hD : X ≤ (forgetUpperIntervalAntichain X D).1.inf id) :
    liftUpperIntervalAntichain X (forgetUpperIntervalAntichain X D) hD = D := by
  apply Subtype.ext
  exact lift_forgetUpperIntervalFamily X D.1

end BooleanAntichainsKernel
