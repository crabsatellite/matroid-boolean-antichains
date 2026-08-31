import BooleanAntichainsKernel.InternalBlockLinearEquiv
import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.GroupTheory.GroupAction.Defs

namespace BooleanAntichainsKernel

open scoped Classical

variable {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]
variable {k : ℕ} {p : Fin k → ℕ}

abbrev InternalProfileStabilizer (D : SizedInternalDecomposition R V p) :=
  MulAction.stabilizer (V ≃ₗ[R] V) D

lemma internalStabilizer_preserves (D : SizedInternalDecomposition R V p)
    (g : InternalProfileStabilizer D) (i : Fin k) :
    (D.1.1 i).map (g.1 : V →ₗ[R] V) = D.1.1 i := by
  have h := MulAction.mem_stabilizer_iff.mp g.2
  exact congrArg (fun E : SizedInternalDecomposition R V p ↦ E.1.1 i) h

/-- Restrict the actual stabilizing automorphism to every actual summand. -/
def internalStabilizerRestrict (D : SizedInternalDecomposition R V p)
    (g : InternalProfileStabilizer D) (i : Fin k) :
    D.1.1 i ≃ₗ[R] D.1.1 i :=
  g.1.ofSubmodules (D.1.1 i) (D.1.1 i) (internalStabilizer_preserves D g i)

@[simp] theorem internalStabilizerRestrict_apply (D : SizedInternalDecomposition R V p)
    (g : InternalProfileStabilizer D) (i : Fin k) (x : D.1.1 i) :
    (internalStabilizerRestrict D g i x : V) = g.1 (x : V) := rfl

/-- The block-diagonal extension fixes each indexed summand, so no
permutation of equal-dimensional summands is inserted into this stabilizer. -/
noncomputable def internalStabilizerExtend (D : SizedInternalDecomposition R V p)
    (e : ∀ i, D.1.1 i ≃ₗ[R] D.1.1 i) : InternalProfileStabilizer D := by
  refine ⟨internalBlockLinearEquiv D.1 D.1 e, MulAction.mem_stabilizer_iff.mpr ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  funext i
  exact internalBlockLinearEquiv_map D.1 D.1 e i

theorem internalStabilizer_extend_restrict (D : SizedInternalDecomposition R V p)
    (g : InternalProfileStabilizer D) :
    internalStabilizerExtend D (internalStabilizerRestrict D g) = g := by
  apply Subtype.ext
  apply internalLinearEquiv_ext D.1
  intro i x
  change internalBlockLinearEquiv D.1 D.1 (internalStabilizerRestrict D g) (x : V) = g.1 (x : V)
  rw [internalBlockLinearEquiv_apply, internalStabilizerRestrict_apply]

theorem internalStabilizer_restrict_extend (D : SizedInternalDecomposition R V p)
    (e : ∀ i, D.1.1 i ≃ₗ[R] D.1.1 i) :
    internalStabilizerRestrict D (internalStabilizerExtend D e) = e := by
  funext i
  apply LinearEquiv.ext
  intro x
  apply Subtype.ext
  change internalBlockLinearEquiv D.1 D.1 e (x : V) = (e i x : V)
  exact internalBlockLinearEquiv_apply D.1 D.1 e i x

/-- The actual profile stabilizer is the product of the component GL
groups, with both inverse maps and the group law proved. -/
noncomputable def internalStabilizerMulEquiv (D : SizedInternalDecomposition R V p) :
    InternalProfileStabilizer D ≃* (∀ i, D.1.1 i ≃ₗ[R] D.1.1 i) where
  toFun := internalStabilizerRestrict D
  invFun := internalStabilizerExtend D
  left_inv := internalStabilizer_extend_restrict D
  right_inv := internalStabilizer_restrict_extend D
  map_mul' g h := by
    funext i
    apply LinearEquiv.ext
    intro x
    apply Subtype.ext
    rfl

end BooleanAntichainsKernel
