import BooleanAntichainsKernel.SubspaceDimensions
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

namespace BooleanAntichainsKernel

open Finset
open scoped Classical

noncomputable instance finiteLinearAutomorphisms {R V : Type*} [Ring R]
    [AddCommGroup V] [Module R V] [Fintype V] : Fintype (V ≃ₗ[R] V) :=
  Fintype.ofInjective (fun g : V ≃ₗ[R] V ↦ (g : V → V)) LinearEquiv.coe_injective

/-- The paper's g_d(q), defined as the actual matrix-GL cardinality. -/
noncomputable def generalLinearCard (K : Type*) [Field K] [Fintype K] (d : ℕ) : ℕ :=
  Nat.card (Matrix.GeneralLinearGroup (Fin d) K)

theorem generalLinearCard_product (K : Type*) [Field K] [Fintype K] (d : ℕ) :
    generalLinearCard K d = ∏ i : Fin d, ((Fintype.card K) ^ d - (Fintype.card K) ^ i.1) :=
  Matrix.card_GL_field (𝔽 := K) d

theorem generalLinearCard_zero (K : Type*) [Field K] [Fintype K] :
    generalLinearCard K 0 = 1 := by
  rw [generalLinearCard_product]
  simp

theorem generalLinearCard_pos (K : Type*) [Field K] [Fintype K] (d : ℕ) :
    0 < generalLinearCard K d := by
  rw [generalLinearCard, Nat.card_eq_fintype_card]
  exact Fintype.card_pos

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- The basis-induced actual group isomorphism from matrix GL to the
automorphism group acting on V; no group size is postulated. -/
noncomputable def matrixGLMulEquivAut :
    Matrix.GeneralLinearGroup (Fin (Module.finrank K V)) K ≃* (V ≃ₗ[K] V) :=
  (Matrix.GeneralLinearGroup.toLin' (Module.finBasis K V)).trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv K V)

theorem linearAutomorphism_card [Fintype K] [Fintype V] :
    Fintype.card (V ≃ₗ[K] V) = generalLinearCard K (Module.finrank K V) := by
  rw [← Nat.card_eq_fintype_card]
  exact (Nat.card_congr (matrixGLMulEquivAut (K := K) (V := V)).toEquiv).symm

end BooleanAntichainsKernel
