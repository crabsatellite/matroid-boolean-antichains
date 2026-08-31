import BooleanAntichainsKernel.InternalBlockLinearEquiv
import Mathlib.Algebra.Group.Action.Pretransitive

namespace BooleanAntichainsKernel

open scoped Classical

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable [FiniteDimensional K V] {k : ℕ} {p : Fin k → ℕ}

/-- An actual ambient GL element, assembled from equal-dimensional
component isomorphisms and the canonical internal-sum maps. -/
noncomputable def sizedInternalTransport (D E : SizedInternalDecomposition K V p) : V ≃ₗ[K] V :=
  internalBlockLinearEquiv D.1 E.1 (fun i ↦
    LinearEquiv.ofFinrankEq (R := K) (D.1.1 i) (E.1.1 i) ((D.2 i).trans (E.2 i).symm))

theorem sizedInternalTransport_smul (D E : SizedInternalDecomposition K V p) :
    sizedInternalTransport D E • D = E := by
  apply Subtype.ext
  apply Subtype.ext
  funext i
  change (D.1.1 i).map (sizedInternalTransport D E : V →ₗ[K] V) = E.1.1 i
  exact internalBlockLinearEquiv_map D.1 E.1 _ i

/-- Pretransitivity on the exact fixed-profile carrier. Its nonemptiness
for positive profiles of total dimension is a separate required producer. -/
instance sizedInternal_isPretransitive (p : Fin k → ℕ) :
    MulAction.IsPretransitive (V ≃ₗ[K] V) (SizedInternalDecomposition K V p) where
  exists_smul_eq D E := ⟨sizedInternalTransport D E, sizedInternalTransport_smul D E⟩

end BooleanAntichainsKernel
