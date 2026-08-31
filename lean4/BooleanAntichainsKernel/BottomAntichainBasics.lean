import BooleanAntichainsKernel.AtomCoatomReconstruction
import BooleanAntichainsKernel.UnorderedFullHeight
import BooleanAntichainsKernel.BottomEmbeddingIntervals

namespace BooleanAntichainsKernel

open Finset
open scoped Classical

abbrev BottomBooleanAntichain (k : ℕ) (L : Type*) [DecidableEq L]
    [Lattice L] [OrderBot L] [OrderTop L] :=
  {C : BooleanAntichain k L // C.1.inf id = ⊥}

variable {L : Type*} [DecidableEq L] [Lattice L] [OrderBot L] [OrderTop L] {k : ℕ}

noncomputable instance [Fintype L] : Fintype (BottomBooleanAntichain k L) := Subtype.fintype _

noncomputable def bottomAntichainTuple (C : BottomBooleanAntichain k L) : Fin k → L :=
  fun i ↦ (canonicalEnumeration C.1 i).1

lemma bottomAntichainTuple_boolean (C : BottomBooleanAntichain k L) :
    IsBooleanTuple (bottomAntichainTuple C) :=
  (isBooleanTuple_iff_antichain_of_equiv C.1.1 (canonicalEnumeration C.1)).mpr C.1.2.2

lemma bottomAntichainTuple_carrier (C : BottomBooleanAntichain k L) :
    orderedCarrier (bottomAntichainTuple C) = C.1.1 :=
  orderedCarrier_of_equiv C.1.1 (canonicalEnumeration C.1)

lemma bottomAntichainTuple_bottom (C : BottomBooleanAntichain k L) :
    commonMeet (bottomAntichainTuple C) = ⊥ :=
  (enumeration_commonMeet C.1.1 (canonicalEnumeration C.1)).trans C.2

noncomputable def bottomAntichainToEmbedding (C : BottomBooleanAntichain k L) :
    BottomTopBooleanEmbedding (Fin k) L :=
  ⟨orderedBooleanToTopEmbedding ⟨bottomAntichainTuple C, bottomAntichainTuple_boolean C⟩, by
    change meetFace (bottomAntichainTuple C) ∅ = ⊥
    rw [meetFace_empty, bottomAntichainTuple_bottom]⟩

theorem bottomAntichainToEmbedding_singleton (C : BottomBooleanAntichain k L) (i : Fin k) :
    (bottomAntichainToEmbedding C).1.1.1 {i} = reconstructedAtom (bottomAntichainTuple C) i :=
  (reconstructedAtom_eq_meetFace_singleton (bottomAntichainTuple C) i).symm

theorem bottomAntichainAtoms_carrier (C : BottomBooleanAntichain k L) :
    antichainAtoms C.1.1 = orderedCarrier (reconstructedAtom (bottomAntichainTuple C)) := by
  rw [← bottomAntichainTuple_carrier C,
    antichainAtoms_orderedCarrier _ (isBooleanTuple_injective (bottomAntichainTuple_boolean C))]

/-- The literal erase/meet and erase/join maps are inverse at Boolean bottom. -/
theorem basisCoatoms_antichainAtoms_of_bottom (C : BottomBooleanAntichain k L) :
    basisCoatoms (antichainAtoms C.1.1) = C.1.1 := by
  rw [bottomAntichainAtoms_carrier C,
    basisCoatoms_orderedCarrier _ (reconstructedAtom_injective (bottomAntichainTuple_boolean C)),
    coatomTuple_reconstructedAtom (bottomAntichainTuple_boolean C) (bottomAntichainTuple_bottom C),
    bottomAntichainTuple_carrier]

noncomputable def bottomAntichainOfEmbedding (f : BottomTopBooleanEmbedding (Fin k) L) :
    BottomBooleanAntichain k L := by
  have hH := topBooleanEmbedding_coatoms_isBoolean f.1
  refine ⟨⟨orderedCarrier (topHomCoatoms f.1.1), orderedCarrier_card hH,
    orderedCarrier_isBoolean hH⟩, ?_⟩
  change (Finset.univ.image (topHomCoatoms f.1.1)).inf id = ⊥
  rw [Finset.inf_image]
  exact (topEmbedding_bottom_coatom_meet f.1).symm.trans f.2

theorem bottomAntichainOfEmbedding_carrier (f : BottomTopBooleanEmbedding (Fin k) L) :
    (bottomAntichainOfEmbedding f).1.1 = orderedCarrier (topHomCoatoms f.1.1) := rfl

end BooleanAntichainsKernel
