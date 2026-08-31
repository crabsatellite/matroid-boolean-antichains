import BooleanAntichainsKernel.UnorderedInternalData
import Mathlib.Data.Fintype.Perm

namespace BooleanAntichainsKernel

open Finset
open scoped Classical

variable {R V : Type*} [Ring R] [AddCommGroup V] [Module R V] {k : ℕ}

abbrev EnumeratedInternalDecomposition (R V : Type*) [Ring R] [AddCommGroup V] [Module R V] (k : ℕ) :=
  Σ D : UnorderedInternalDecomposition R V k, (Fin k ≃ D.1)

def enumeratedInternalToOrdered (x : EnumeratedInternalDecomposition R V k) :
    OrderedInternalDecomposition R V k := orderInternalFamily x.1 x.2

noncomputable def orderedInternalToEnumerated (D : OrderedInternalDecomposition R V k) :
    EnumeratedInternalDecomposition R V k :=
  ⟨forgetOrderedInternal D, indexEquivCarrier D.1 (orderedInternal_injective D)⟩

theorem enumeratedInternal_ordered_roundtrip (D : OrderedInternalDecomposition R V k) :
    enumeratedInternalToOrdered (orderedInternalToEnumerated D) = D := by
  apply Subtype.ext
  funext i
  rfl

theorem enumeratedInternalToOrdered_injective :
    Function.Injective (enumeratedInternalToOrdered (R := R) (V := V) (k := k)) := by
  rintro ⟨A, e⟩ ⟨B, f⟩ h
  have hcar : A.1 = B.1 := by
    calc
      _ = orderedCarrier (orderInternalFamily A e).1 := (orderInternalFamily_carrier A e).symm
      _ = orderedCarrier (orderInternalFamily B f).1 :=
        congrArg (fun D : OrderedInternalDecomposition R V k ↦ orderedCarrier D.1) h
      _ = B.1 := orderInternalFamily_carrier B f
  have hAB : A = B := Subtype.ext hcar
  cases hAB
  apply congrArg (Sigma.mk A)
  apply Equiv.ext
  intro i
  apply Subtype.ext
  exact congrArg (fun D : OrderedInternalDecomposition R V k ↦ D.1 i) h

noncomputable def enumeratedInternalEquivOrdered :
    EnumeratedInternalDecomposition R V k ≃ OrderedInternalDecomposition R V k :=
  Equiv.ofBijective enumeratedInternalToOrdered
    ⟨enumeratedInternalToOrdered_injective,
      fun D ↦ ⟨orderedInternalToEnumerated D, enumeratedInternal_ordered_roundtrip D⟩⟩

/-- The k-factorial fibre counts permutations of actual distinct nonzero
summands, including when some of their dimensions happen to coincide. -/
theorem orderedInternal_count_eq_unordered_mul_factorial [Fintype V] :
    Fintype.card (OrderedInternalDecomposition R V k) =
      Fintype.card (UnorderedInternalDecomposition R V k) * k.factorial := by
  calc
    _ = Fintype.card (EnumeratedInternalDecomposition R V k) :=
      (Fintype.card_congr enumeratedInternalEquivOrdered).symm
    _ = ∑ D : UnorderedInternalDecomposition R V k, Fintype.card (Fin k ≃ D.1) := Fintype.card_sigma
    _ = ∑ _D : UnorderedInternalDecomposition R V k, k.factorial := by
      apply Finset.sum_congr rfl
      intro D _
      simpa using Fintype.card_equiv (canonicalInternalEnumeration D)
    _ = _ := by simp

theorem unorderedInternal_count_eq_ordered_div_factorial [Fintype V] :
    Fintype.card (UnorderedInternalDecomposition R V k) =
      Fintype.card (OrderedInternalDecomposition R V k) / k.factorial := by
  rw [orderedInternal_count_eq_unordered_mul_factorial, Nat.mul_div_cancel _ (Nat.factorial_pos k)]

end BooleanAntichainsKernel
