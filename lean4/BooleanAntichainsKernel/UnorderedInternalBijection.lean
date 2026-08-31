import BooleanAntichainsKernel.UnorderedInternalData
import BooleanAntichainsKernel.BottomAntichainBasics

namespace BooleanAntichainsKernel

open Finset
open scoped Classical

variable {R V : Type*} [Ring R] [AddCommGroup V] [Module R V] {k : ℕ}

noncomputable def bottomAntichainToUnorderedInternal
    (C : BottomBooleanAntichain k (Submodule R V)) : UnorderedInternalDecomposition R V k :=
  forgetOrderedInternal (bottomEmbeddingToInternal (bottomAntichainToEmbedding C))

/-- Forward map is the actual unordered family of reconstructed atoms. -/
theorem bottomAntichainToUnorderedInternal_val
    (C : BottomBooleanAntichain k (Submodule R V)) :
    (bottomAntichainToUnorderedInternal C).1 = antichainAtoms C.1.1 := by
  have hfun : (bottomEmbeddingToInternal (bottomAntichainToEmbedding C)).1 =
      reconstructedAtom (bottomAntichainTuple C) := by
    funext i
    exact bottomAntichainToEmbedding_singleton C i
  calc
    _ = orderedCarrier (bottomEmbeddingToInternal (bottomAntichainToEmbedding C)).1 := rfl
    _ = orderedCarrier (reconstructedAtom (bottomAntichainTuple C)) := congrArg orderedCarrier hfun
    _ = antichainAtoms C.1.1 := (bottomAntichainAtoms_carrier C).symm

noncomputable def unorderedInternalToBottomAntichain (D : UnorderedInternalDecomposition R V k) :
    BottomBooleanAntichain k (Submodule R V) :=
  bottomAntichainOfEmbedding (orderUnorderedInternal D).toBottomEmbedding

/-- Inverse map is the actual family of joins after erasing one summand. -/
theorem unorderedInternalToBottomAntichain_val (D : UnorderedInternalDecomposition R V k) :
    (unorderedInternalToBottomAntichain D).1.1 = basisCoatoms D.1 := by
  have hcar : orderedCarrier (orderUnorderedInternal D).1 = D.1 :=
    orderInternalFamily_carrier D (canonicalInternalEnumeration D)
  calc
    _ = orderedCarrier (coatomTuple (orderUnorderedInternal D).1) := rfl
    _ = basisCoatoms (orderedCarrier (orderUnorderedInternal D).1) :=
      (basisCoatoms_orderedCarrier _ (orderedInternal_injective _)).symm
    _ = basisCoatoms D.1 := congrArg basisCoatoms hcar

theorem antichainAtoms_basisCoatoms_internal (D : UnorderedInternalDecomposition R V k) :
    antichainAtoms (basisCoatoms D.1) = D.1 := by
  let U := orderUnorderedInternal D
  have hcar : orderedCarrier U.1 = D.1 :=
    orderInternalFamily_carrier D (canonicalInternalEnumeration D)
  have hmeet : ∀ S T : Finset (Fin k), S.sup U.1 ⊓ T.sup U.1 = (S ∩ T).sup U.1 :=
    fun S T ↦ (U.sup_inter S T).symm
  have hH : IsBooleanTuple (coatomTuple U.1) :=
    coatomTuple_isBoolean U.1 U.sup_univ hmeet U.sup_injective
  calc
    _ = antichainAtoms (orderedCarrier (coatomTuple U.1)) := by
      rw [← hcar, basisCoatoms_orderedCarrier U.1 (orderedInternal_injective U)]
    _ = orderedCarrier (reconstructedAtom (coatomTuple U.1)) :=
      antichainAtoms_orderedCarrier _ (isBooleanTuple_injective hH)
    _ = orderedCarrier U.1 := by rw [reconstructedAtom_coatomTuple U.1 U.sup_univ hmeet]
    _ = D.1 := hcar

theorem unorderedInternal_antichain_internal (D : UnorderedInternalDecomposition R V k) :
    bottomAntichainToUnorderedInternal (unorderedInternalToBottomAntichain D) = D := by
  apply Subtype.ext
  rw [bottomAntichainToUnorderedInternal_val, unorderedInternalToBottomAntichain_val,
    antichainAtoms_basisCoatoms_internal]

theorem bottomAntichain_internal_antichain (C : BottomBooleanAntichain k (Submodule R V)) :
    unorderedInternalToBottomAntichain (bottomAntichainToUnorderedInternal C) = C := by
  apply Subtype.ext
  apply Subtype.ext
  rw [unorderedInternalToBottomAntichain_val, bottomAntichainToUnorderedInternal_val,
    basisCoatoms_antichainAtoms_of_bottom]

/-- The exact unordered bottom-zero Boolean/internal-direct-sum bijection. -/
noncomputable def bottomAntichainEquivUnorderedInternal :
    BottomBooleanAntichain k (Submodule R V) ≃ UnorderedInternalDecomposition R V k where
  toFun := bottomAntichainToUnorderedInternal
  invFun := unorderedInternalToBottomAntichain
  left_inv := bottomAntichain_internal_antichain
  right_inv := unorderedInternal_antichain_internal

end BooleanAntichainsKernel
