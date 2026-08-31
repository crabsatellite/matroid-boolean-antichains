import BooleanAntichainsKernel.AntichainBottomFibres
import BooleanAntichainsKernel.SubspaceQuotientEmbedding

namespace BooleanAntichainsKernel

open Finset
open scoped Classical

variable {R V : Type*} [Ring R] [AddCommGroup V] [Module R V] (X : Submodule R V)

local instance : Fact (X ≤ (⊤ : Submodule R V)) := ⟨le_top⟩

def subspaceIntervalQuotientIso :
    Set.Icc X (⊤ : Submodule R V) ≃o Submodule R (V ⧸ X) :=
  (iccTopOrderIsoIci X).trans X.comapMkQRelIso.symm

@[simp] theorem subspaceIntervalQuotientIso_apply (U : Set.Icc X (⊤ : Submodule R V)) :
    subspaceIntervalQuotientIso X U = U.1.map X.mkQ := rfl

@[simp] theorem subspaceIntervalQuotientIso_symm_apply (U : Submodule R (V ⧸ X)) :
    ((subspaceIntervalQuotientIso X).symm U).1 = U.comap X.mkQ := rfl

lemma mapUpperFamily_quotient (D : Finset (Set.Icc X (⊤ : Submodule R V))) :
    mapFamily (subspaceIntervalQuotientIso X) D =
      (forgetUpperIntervalFamily X D).image (fun U ↦ U.map X.mkQ) := by
  unfold mapFamily forgetUpperIntervalFamily
  rw [Equiv.finsetCongr_apply, Finset.map_eq_image, Finset.image_image]
  rfl

lemma forgetMapUpperFamily_quotient (D : Finset (Submodule R (V ⧸ X))) :
    forgetUpperIntervalFamily X (mapFamily (subspaceIntervalQuotientIso X).symm D) =
      D.image (fun U ↦ U.comap X.mkQ) := by
  unfold mapFamily forgetUpperIntervalFamily
  rw [Equiv.finsetCongr_apply, Finset.map_eq_image, Finset.image_image]
  rfl

variable [Fintype V] {k : ℕ}

noncomputable def subspaceAntichainFibreEquivQuotient :
    BooleanAntichainAtBottom k (Submodule R V) X ≃
      BottomBooleanAntichain k (Submodule R (V ⧸ X)) :=
  (booleanAntichainAtBottomEquivUpper X).trans
    (bottomAntichainOrderIsoEquiv (subspaceIntervalQuotientIso X) k)

/-- The unordered quotient family consists of the literal images H/X. -/
theorem subspaceAntichainFibreEquivQuotient_val
    (C : BooleanAntichainAtBottom k (Submodule R V) X) :
    (subspaceAntichainFibreEquivQuotient X C).1.1 =
      C.1.1.image (fun U ↦ U.map X.mkQ) := by
  change mapFamily (subspaceIntervalQuotientIso X) (liftUpperIntervalAntichain X C.1 C.2.ge).1 = _
  rw [mapUpperFamily_quotient]
  exact congrArg (fun A : Finset (Submodule R V) ↦ A.image (fun U ↦ U.map X.mkQ))
    (congrArg Subtype.val (forget_liftUpperIntervalAntichain X C.1 C.2.ge))

theorem subspaceAntichainFibreEquivQuotient_symm_val
    (D : BottomBooleanAntichain k (Submodule R (V ⧸ X))) :
    ((subspaceAntichainFibreEquivQuotient X).symm D).1.1 =
      D.1.1.image (fun U ↦ U.comap X.mkQ) := by
  change forgetUpperIntervalFamily X
    (mapFamily (subspaceIntervalQuotientIso X).symm D.1.1) = _
  exact forgetMapUpperFamily_quotient X D.1.1

/-- Recovering atoms commutes with the same actual quotient map. -/
theorem subspaceAntichainFibre_atoms
    (C : BooleanAntichainAtBottom k (Submodule R V) X) :
    antichainAtoms (subspaceAntichainFibreEquivQuotient X C).1.1 =
      (antichainAtoms C.1.1).image (fun U ↦ U.map X.mkQ) := by
  change antichainAtoms
    (mapFamily (subspaceIntervalQuotientIso X) (liftUpperIntervalAntichain X C.1 C.2.ge).1) = _
  rw [antichainAtoms_mapFamily, mapUpperFamily_quotient, forgetUpperIntervalFamily_atoms]
  exact congrArg (fun A : Finset (Submodule R V) ↦
    (antichainAtoms A).image (fun U ↦ U.map X.mkQ))
    (congrArg Subtype.val (forget_liftUpperIntervalAntichain X C.1 C.2.ge))

end BooleanAntichainsKernel
