import BooleanAntichainsKernel.SubspaceDimensions

namespace BooleanAntichainsKernel

open Finset
open scoped Classical

variable {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]

lemma isInternal_reindex_iff {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (e : ι ≃ κ) (U : κ → Submodule R V) :
    DirectSum.IsInternal (fun i ↦ U (e i)) ↔ DirectSum.IsInternal U := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top,
    DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top, e.iSup_comp]
  constructor
  · rintro ⟨hi, hs⟩
    exact ⟨hi.comp' e.surjective, hs⟩
  · rintro ⟨hi, hs⟩
    exact ⟨hi.comp e.injective, hs⟩

/-- The literal finite set of nonzero summands; no ordering is part of this carrier. -/
abbrev UnorderedInternalDecomposition (R V : Type*) [Ring R] [AddCommGroup V] [Module R V] (k : ℕ) :=
  {A : Finset (Submodule R V) //
    A.card = k ∧ DirectSum.IsInternal (fun U : A ↦ U.1) ∧ ∀ U ∈ A, U ≠ ⊥}

noncomputable instance [Fintype V] (k : ℕ) : Fintype (UnorderedInternalDecomposition R V k) :=
  Subtype.fintype _

variable {k : ℕ}

def orderInternalFamily (D : UnorderedInternalDecomposition R V k) (e : Fin k ≃ D.1) :
    OrderedInternalDecomposition R V k :=
  ⟨fun i ↦ (e i).1,
    (isInternal_reindex_iff e (fun U : D.1 ↦ U.1)).mpr D.2.2.1,
    fun i ↦ D.2.2.2 (e i).1 (e i).2⟩

noncomputable def canonicalInternalEnumeration (D : UnorderedInternalDecomposition R V k) :
    Fin k ≃ D.1 := (Finset.equivFinOfCardEq D.2.1).symm

noncomputable def orderUnorderedInternal (D : UnorderedInternalDecomposition R V k) :
    OrderedInternalDecomposition R V k := orderInternalFamily D (canonicalInternalEnumeration D)

lemma orderedInternal_injective (D : OrderedInternalDecomposition R V k) : Function.Injective D.1 :=
  D.2.1.submodule_iSupIndep.injective D.2.2

noncomputable def forgetOrderedInternal (D : OrderedInternalDecomposition R V k) :
    UnorderedInternalDecomposition R V k := by
  let A := orderedCarrier D.1
  let e : Fin k ≃ A := indexEquivCarrier D.1 (orderedInternal_injective D)
  have hcard : A.card = k := by
    simp only [A, orderedCarrier, Finset.card_image_of_injective _ (orderedInternal_injective D),
      Finset.card_univ, Fintype.card_fin]
  have hint : DirectSum.IsInternal (fun U : A ↦ U.1) :=
    (isInternal_reindex_iff e (fun U : A ↦ U.1)).mp D.2.1
  refine ⟨A, hcard, hint, ?_⟩
  intro U hU
  rcases Finset.mem_image.mp hU with ⟨i, _, rfl⟩
  exact D.2.2 i

theorem forgetOrderedInternal_val (D : OrderedInternalDecomposition R V k) :
    (forgetOrderedInternal D).1 = orderedCarrier D.1 := rfl

theorem orderInternalFamily_carrier (D : UnorderedInternalDecomposition R V k) (e : Fin k ≃ D.1) :
    orderedCarrier (orderInternalFamily D e).1 = D.1 :=
  orderedCarrier_of_equiv D.1 e

theorem forget_orderInternalFamily (D : UnorderedInternalDecomposition R V k) (e : Fin k ≃ D.1) :
    forgetOrderedInternal (orderInternalFamily D e) = D := by
  apply Subtype.ext
  exact orderInternalFamily_carrier D e

theorem forget_orderUnorderedInternal (D : UnorderedInternalDecomposition R V k) :
    forgetOrderedInternal (orderUnorderedInternal D) = D :=
  forget_orderInternalFamily D (canonicalInternalEnumeration D)

end BooleanAntichainsKernel
