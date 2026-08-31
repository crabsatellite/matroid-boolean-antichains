import BooleanAntichainsKernel.InternalLinearAction
import Mathlib.LinearAlgebra.DFinsupp

namespace BooleanAntichainsKernel

open scoped Classical DirectSum

variable {R V W : Type*} [Ring R] [AddCommGroup V] [Module R V]
variable [AddCommGroup W] [Module R W] {k : ℕ}

/-- Extend the actual component isomorphisms through the two canonical
internal-sum maps, as in the transitivity argument. -/
noncomputable def internalBlockLinearEquiv
    (D : OrderedInternalDecomposition R V k) (E : OrderedInternalDecomposition R W k)
    (e : ∀ i, D.1 i ≃ₗ[R] E.1 i) : V ≃ₗ[R] W :=
  D.sumLinearEquiv.symm.trans ((DFinsupp.mapRange.linearEquiv e).trans E.sumLinearEquiv)

lemma internalBlockMap_of
    (D : OrderedInternalDecomposition R V k) (E : OrderedInternalDecomposition R W k)
    (e : ∀ i, D.1 i ≃ₗ[R] E.1 i) (i : Fin k) (x : D.1 i) :
    DFinsupp.mapRange.linearEquiv e (DirectSum.of (fun i ↦ D.1 i) i x) =
      DirectSum.of (fun i ↦ E.1 i) i (e i x) :=
  DFinsupp.mapRange_single (hf := fun j ↦ (e j).map_zero)

theorem internalBlockLinearEquiv_apply
    (D : OrderedInternalDecomposition R V k) (E : OrderedInternalDecomposition R W k)
    (e : ∀ i, D.1 i ≃ₗ[R] E.1 i) (i : Fin k) (x : D.1 i) :
    internalBlockLinearEquiv D E e (x : V) = (e i x : W) := by
  have hx : D.sumLinearEquiv.symm (x : V) = DirectSum.of (fun i ↦ D.1 i) i x := by
    apply D.sumLinearEquiv.injective
    rw [D.sumLinearEquiv.apply_symm_apply, D.sumLinearEquiv_of]
  change E.sumLinearEquiv (DFinsupp.mapRange.linearEquiv e (D.sumLinearEquiv.symm (x : V))) = _
  rw [hx, internalBlockMap_of, E.sumLinearEquiv_of]

theorem internalBlockLinearEquiv_map
    (D : OrderedInternalDecomposition R V k) (E : OrderedInternalDecomposition R W k)
    (e : ∀ i, D.1 i ≃ₗ[R] E.1 i) (i : Fin k) :
    (D.1 i).map (internalBlockLinearEquiv D E e : V →ₗ[R] W) = E.1 i := by
  apply le_antisymm
  · intro y hy
    rcases Submodule.mem_map.mp hy with ⟨x, hx, rfl⟩
    change internalBlockLinearEquiv D E e x ∈ E.1 i
    rw [internalBlockLinearEquiv_apply D E e i ⟨x, hx⟩]
    exact (e i ⟨x, hx⟩).2
  · intro y hy
    let x : D.1 i := (e i).symm ⟨y, hy⟩
    refine Submodule.mem_map.mpr ⟨(x : V), x.2, ?_⟩
    change internalBlockLinearEquiv D E e (x : V) = y
    rw [internalBlockLinearEquiv_apply]
    exact congrArg Subtype.val ((e i).apply_symm_apply ⟨y, hy⟩)

/-- A linear equivalence is determined by its restrictions to the actual
internal summands. This will close the stabilizer inverse law. -/
theorem internalLinearEquiv_ext (D : OrderedInternalDecomposition R V k)
    {g h : V ≃ₗ[R] W} (heq : ∀ i (x : D.1 i), g (x : V) = h (x : V)) : g = h := by
  apply LinearEquiv.ext
  intro v
  obtain ⟨x, rfl⟩ := D.sumLinearEquiv.surjective v
  induction x using DirectSum.induction_on with
  | zero => simp
  | of i x => simpa only [D.sumLinearEquiv_of] using heq i x
  | add x y hx hy => simp only [map_add, hx, hy]

end BooleanAntichainsKernel
