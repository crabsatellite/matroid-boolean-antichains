import BooleanAntichainsKernel.SubspaceFrames
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Data.Rat.Cast.Order

namespace BooleanAntichainsKernel

open Finset
open scoped Classical

/-- The finite product counting independent frames; subtraction is in ℕ. -/
def frameProduct (q n d : ℕ) : ℕ := ∏ i : Fin d, (q ^ n - q ^ i.1)

/-- The standard Gaussian product ratio, independent of the subspace carrier.
Its equality to the literal subspace count is proved below. -/
def gaussianCoefficient (q n d : ℕ) : ℚ :=
  (frameProduct q n d : ℚ) / (frameProduct q d d : ℚ)

theorem frameProduct_diagonal (K : Type*) [Field K] [Fintype K] (d : ℕ) :
    frameProduct (Fintype.card K) d d = generalLinearCard K d :=
  (generalLinearCard_product K d).symm

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Codimension is measured by the genuine quotient V/X. -/
def CodimensionSubspace (K V : Type*) [Field K] [AddCommGroup V] [Module K V] (d : ℕ) :=
  {X : Submodule K V // Module.finrank K (V ⧸ X) = d}

noncomputable instance [Fintype V] (d : ℕ) : Fintype (CodimensionSubspace K V d) :=
  inferInstanceAs (Fintype {X : Submodule K V // Module.finrank K (V ⧸ X) = d})

variable [FiniteDimensional K V]

/-- The actual annihilator/coannihilator maps, with quotient dimension
transported through a proved linear equivalence. -/
noncomputable def codimensionAnnihilatorEquiv (d : ℕ) :
    CodimensionSubspace K V d ≃ DimensionSubspace K (Module.Dual K V) d where
  toFun X := ⟨X.1.dualAnnihilator,
    (Subspace.quotEquivAnnihilator X.1).finrank_eq.symm.trans X.2⟩
  invFun W := ⟨W.1.dualCoannihilator, by
    rw [(Subspace.quotEquivAnnihilator W.1.dualCoannihilator).finrank_eq,
      Subspace.dualCoannihilator_dualAnnihilator_eq]
    exact W.2⟩
  left_inv _ := Subtype.ext Subspace.dualAnnihilator_dualCoannihilator_eq
  right_inv _ := Subtype.ext Subspace.dualCoannihilator_dualAnnihilator_eq

theorem codimensionAnnihilatorEquiv_apply (d : ℕ) (X : CodimensionSubspace K V d) :
    (codimensionAnnihilatorEquiv d X).1 = X.1.dualAnnihilator := rfl

theorem codimensionAnnihilatorEquiv_symm_apply (d : ℕ)
    (W : DimensionSubspace K (Module.Dual K V) d) :
    ((codimensionAnnihilatorEquiv d).symm W).1 = W.1.dualCoannihilator := rfl

variable [Fintype K] [Fintype V]

theorem dimensionSubspace_gaussian {d : ℕ} (hd : d ≤ Module.finrank K V) :
    (Fintype.card (DimensionSubspace K V d) : ℚ) =
      gaussianCoefficient (Fintype.card K) (Module.finrank K V) d := by
  rw [gaussianCoefficient, frameProduct_diagonal]
  apply (eq_div_iff (Nat.cast_ne_zero.mpr (Nat.ne_of_gt (generalLinearCard_pos K d)))).mpr
  exact_mod_cast dimensionSubspace_card_mul hd

/-- The Gaussian coefficient counts the literal codimension-d subspaces;
no symmetry identity or external count is inserted as a premise. -/
theorem codimensionSubspace_gaussian {d : ℕ} (hd : d ≤ Module.finrank K V) :
    (Fintype.card (CodimensionSubspace K V d) : ℚ) =
      gaussianCoefficient (Fintype.card K) (Module.finrank K V) d := by
  letI : Fintype (Module.Dual K V) :=
    Fintype.ofInjective (fun f : Module.Dual K V ↦ (f : V → K)) LinearMap.coe_injective
  rw [Fintype.card_congr (codimensionAnnihilatorEquiv (K := K) (V := V) d)]
  have hd' : d ≤ Module.finrank K (Module.Dual K V) := by
    simpa only [Subspace.dual_finrank_eq] using hd
  simpa only [Subspace.dual_finrank_eq] using
    (dimensionSubspace_gaussian (K := K) (V := Module.Dual K V) hd')

theorem standardCodimensionSubspace_gaussian (K : Type*) [Field K] [Fintype K]
    (n d : ℕ) (hd : d ≤ n) :
    (Fintype.card (CodimensionSubspace K (Fin n → K) d) : ℚ) =
      gaussianCoefficient (Fintype.card K) n d := by
  simpa only [Module.finrank_fin_fun] using
    (codimensionSubspace_gaussian (K := K) (V := Fin n → K) (d := d)
      (by simpa only [Module.finrank_fin_fun] using hd))

end BooleanAntichainsKernel
