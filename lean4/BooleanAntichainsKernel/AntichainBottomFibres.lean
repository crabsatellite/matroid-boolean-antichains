import BooleanAntichainsKernel.BottomAntichainBasics
import BooleanAntichainsKernel.UpperIntervalAntichains

namespace BooleanAntichainsKernel

open Finset
open scoped Classical

abbrev BooleanAntichainAtBottom (k : ℕ) (L : Type*) [DecidableEq L]
    [Lattice L] [OrderBot L] [OrderTop L] (X : L) :=
  {C : BooleanAntichain k L // C.1.inf id = X}

variable {L K : Type*} [DecidableEq L] [Lattice L] [OrderBot L] [OrderTop L]
variable [DecidableEq K] [Lattice K] [OrderBot K] [OrderTop K] {k : ℕ}

def bottomAntichainOrderIsoEquiv (e : L ≃o K) (k : ℕ) :
    BottomBooleanAntichain k L ≃ BottomBooleanAntichain k K :=
  (booleanAntichainOrderIsoEquiv e k).subtypeEquiv (fun C ↦ by
    change C.1.inf id = ⊥ ↔ (mapFamily e C.1).inf id = ⊥
    have hmap : (mapFamily e C.1).inf id = e (C.1.inf id) := by
      rw [mapFamily, Equiv.finsetCongr_apply, Finset.inf_map]
      exact (map_finset_inf e C.1 id).symm
    rw [hmap, ← e.map_bot, e.injective.eq_iff])

variable (X : L)

local instance : Fact (X ≤ (⊤ : L)) := ⟨le_top⟩

def iccTopOrderIsoIci : Set.Icc X (⊤ : L) ≃o Set.Ici X where
  toFun U := ⟨U.1, U.2.1⟩
  invFun U := ⟨U.1, U.2, le_top⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

omit [OrderBot L] in
lemma forgetUpperIntervalFamily_atoms (D : Finset (Set.Icc X (⊤ : L))) :
    forgetUpperIntervalFamily X (antichainAtoms D) =
      antichainAtoms (forgetUpperIntervalFamily X D) := by
  unfold forgetUpperIntervalFamily antichainAtoms
  rw [Finset.image_image, Finset.image_image]
  apply Finset.image_congr
  intro H _
  change ((D.erase H).inf id).1 = ((D.image Subtype.val).erase H.1).inf id
  rw [← Finset.image_erase Subtype.val_injective, Finset.inf_image]
  exact upperInterval_val_inf X (D.erase H) id

variable [Fintype L]

noncomputable instance : Fintype (BooleanAntichainAtBottom k L X) := Subtype.fintype _

noncomputable def bottomFibreToUpper (C : BooleanAntichainAtBottom k L X) :
    BottomBooleanAntichain k (Set.Icc X (⊤ : L)) := by
  let D := liftUpperIntervalAntichain X C.1 C.2.ge
  have hf : forgetUpperIntervalAntichain X D = C.1 :=
    forget_liftUpperIntervalAntichain X C.1 C.2.ge
  have hc : forgetUpperIntervalFamily X D.1 = C.1.1 := congrArg Subtype.val hf
  refine ⟨D, ?_⟩
  apply Subtype.ext
  calc
    _ = (forgetUpperIntervalFamily X D.1).inf id := (forgetUpperIntervalFamily_inf X D.1).symm
    _ = C.1.1.inf id := congrArg (fun S : Finset L ↦ S.inf id) hc
    _ = X := C.2

noncomputable def upperBottomToFibre (D : BottomBooleanAntichain k (Set.Icc X (⊤ : L))) :
    BooleanAntichainAtBottom k L X :=
  ⟨forgetUpperIntervalAntichain X D.1,
    (forgetUpperIntervalFamily_inf X D.1.1).trans (congrArg Subtype.val D.2)⟩

noncomputable def booleanAntichainAtBottomEquivUpper :
    BooleanAntichainAtBottom k L X ≃ BottomBooleanAntichain k (Set.Icc X (⊤ : L)) where
  toFun := bottomFibreToUpper X
  invFun := upperBottomToFibre X
  left_inv C := by
    apply Subtype.ext
    exact forget_liftUpperIntervalAntichain X C.1 C.2.ge
  right_inv D := by
    apply Subtype.ext
    exact lift_forgetUpperIntervalAntichain X D.1 (forgetUpperIntervalAntichain_lower X D.1)

def booleanAntichainBottomSigmaEquiv :
    (Σ X : L, BooleanAntichainAtBottom k L X) ≃ BooleanAntichain k L :=
  Equiv.sigmaFiberEquiv (fun C : BooleanAntichain k L ↦ C.1.inf id)

end BooleanAntichainsKernel
