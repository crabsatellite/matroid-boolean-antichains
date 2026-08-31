import BooleanAntichainsKernel.InternalProfileExistence
import BooleanAntichainsKernel.InternalStabilizer
import BooleanAntichainsKernel.LinearAutomorphismCard
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

namespace BooleanAntichainsKernel

open Finset
open scoped Classical

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable [FiniteDimensional K V] {k : ℕ} {p : Fin k → ℕ}

noncomputable def internalProfileOrbitEquiv (D : SizedInternalDecomposition K V p) :
    MulAction.orbit (V ≃ₗ[K] V) D ≃ SizedInternalDecomposition K V p where
  toFun E := E.1
  invFun E := ⟨E, ⟨sizedInternalTransport D E, sizedInternalTransport_smul D E⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable [Fintype K] [Fintype V]

theorem internalStabilizer_card (D : SizedInternalDecomposition K V p) :
    Fintype.card (InternalProfileStabilizer D) = ∏ i, generalLinearCard K (p i) := by
  rw [Fintype.card_congr (internalStabilizerMulEquiv D).toEquiv, Fintype.card_pi]
  apply Finset.prod_congr rfl
  intro i _
  rw [linearAutomorphism_card, D.2 i]

/-- The orbit-stabilizer equation for the actual GL action and the actual
fixed-profile carrier, with the proved product-GL stabilizer consumed. -/
theorem internalProfile_count_mul (D : SizedInternalDecomposition K V p) :
    Fintype.card (SizedInternalDecomposition K V p) * (∏ i, generalLinearCard K (p i)) =
      generalLinearCard K (Module.finrank K V) := by
  have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (V ≃ₗ[K] V) D
  rw [Fintype.card_congr (internalProfileOrbitEquiv D), internalStabilizer_card D,
    linearAutomorphism_card] at h
  exact h

theorem internalProfile_count (D : SizedInternalDecomposition K V p) :
    Fintype.card (SizedInternalDecomposition K V p) =
      generalLinearCard K (Module.finrank K V) / ∏ i, generalLinearCard K (p i) := by
  have hp : 0 < ∏ i, generalLinearCard K (p i) :=
    Finset.prod_pos (fun i _ ↦ generalLinearCard_pos K (p i))
  calc
    _ = (Fintype.card (SizedInternalDecomposition K V p) * ∏ i, generalLinearCard K (p i)) /
          (∏ i, generalLinearCard K (p i)) := (Nat.mul_div_cancel _ hp).symm
    _ = _ := by rw [internalProfile_count_mul D]

theorem internalProfile_count_rational (D : SizedInternalDecomposition K V p) :
    (Fintype.card (SizedInternalDecomposition K V p) : ℚ) =
      (generalLinearCard K (Module.finrank K V) : ℚ) / ∏ i, (generalLinearCard K (p i) : ℚ) := by
  have hp : 0 < ∏ i, generalLinearCard K (p i) :=
    Finset.prod_pos (fun i _ ↦ generalLinearCard_pos K (p i))
  have hden : (∏ i, (generalLinearCard K (p i) : ℚ)) ≠ 0 := by
    rw [← Nat.cast_prod]
    exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt hp)
  apply (eq_div_iff hden).mpr
  exact_mod_cast internalProfile_count_mul D

/-- No nonempty-profile premise is left unpaid: the actual decomposition
is constructed for every positive composition of the ambient dimension. -/
theorem sizedInternal_count_of_profile (p : Fin k → ℕ) (hp : ∀ i, 1 ≤ p i)
    (hs : (∑ i, p i) = Module.finrank K V) :
    Fintype.card (SizedInternalDecomposition K V p) =
      generalLinearCard K (Module.finrank K V) / ∏ i, generalLinearCard K (p i) :=
  internalProfile_count (sizedInternalOfProfile p hp hs)

theorem sizedInternal_count_of_profile_rational (p : Fin k → ℕ) (hp : ∀ i, 1 ≤ p i)
    (hs : (∑ i, p i) = Module.finrank K V) :
    (Fintype.card (SizedInternalDecomposition K V p) : ℚ) =
      (generalLinearCard K (Module.finrank K V) : ℚ) / ∏ i, (generalLinearCard K (p i) : ℚ) :=
  internalProfile_count_rational (sizedInternalOfProfile p hp hs)

end BooleanAntichainsKernel
