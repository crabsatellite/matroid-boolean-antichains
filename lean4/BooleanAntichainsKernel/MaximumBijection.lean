import BooleanAntichainsKernel.AtomCoatomReconstruction
import BooleanAntichainsKernel.BasisSpan

/-! The two inverse unordered maps of the maximum-antichain theorem.
Both maps below literally erase one member and take the indicated meet/join.
The standard Tutte-polynomial evaluation is a separate consumer. -/

namespace BooleanAntichainsKernel

open Finset

variable {α : Type*} [Fintype α]

abbrev SimplifiedBasis (M : Matroid α) :=
  {A : Finset (MatroidFlat M) // IsSimplifiedBasis M A}

abbrev MaximumBooleanAntichain (M : Matroid α) :=
  BooleanAntichain (MatroidFlat.rank (⊤ : MatroidFlat M)) (MatroidFlat M)

noncomputable instance {M : Matroid α} : Fintype (SimplifiedBasis M) := by
  classical
  exact Subtype.fintype _

variable {M : Matroid α}

noncomputable def simplifiedBasisEnumeration (A : SimplifiedBasis M) :
    Fin (MatroidFlat.rank (⊤ : MatroidFlat M)) ≃ A.1 :=
  (Finset.equivFinOfCardEq A.2.2.1).symm

noncomputable def simplifiedBasisTuple (A : SimplifiedBasis M) :
    Fin (MatroidFlat.rank (⊤ : MatroidFlat M)) → MatroidFlat M :=
  fun i ↦ (simplifiedBasisEnumeration A i).1

omit [Fintype α] in
lemma simplifiedBasisTuple_injective (A : SimplifiedBasis M) :
    Function.Injective (simplifiedBasisTuple A) :=
  Subtype.val_injective.comp (simplifiedBasisEnumeration A).injective

lemma simplifiedBasisTuple_carrier (A : SimplifiedBasis M) :
    orderedCarrier (simplifiedBasisTuple A) = A.1 :=
  orderedCarrier_of_equiv A.1 (simplifiedBasisEnumeration A)

omit [Fintype α] in
lemma simplifiedBasisTuple_rank (A : SimplifiedBasis M) (i) :
    MatroidFlat.rank (simplifiedBasisTuple A i) = 1 :=
  A.2.1 _ (simplifiedBasisEnumeration A i).2

lemma simplifiedBasisTuple_sup (A : SimplifiedBasis M) :
    Finset.univ.sup (simplifiedBasisTuple A) = ⊤ := by
  have hsup := Finset.sup_image
    (Finset.univ : Finset (Fin (MatroidFlat.rank (⊤ : MatroidFlat M))))
    (simplifiedBasisTuple A) id
  have hcarrier : Finset.univ.image (simplifiedBasisTuple A) = A.1 := simplifiedBasisTuple_carrier A
  rw [hcarrier] at hsup
  exact hsup.symm.trans A.2.2.2

lemma simplifiedBasisTuple_span (A : SimplifiedBasis M) :
    (∀ S T : Finset (Fin (MatroidFlat.rank (⊤ : MatroidFlat M))),
      S.sup (simplifiedBasisTuple A) ⊓ T.sup (simplifiedBasisTuple A) =
      (S ∩ T).sup (simplifiedBasisTuple A)) ∧
    Function.Injective (fun S : Finset (Fin (MatroidFlat.rank (⊤ : MatroidFlat M))) ↦
      S.sup (simplifiedBasisTuple A)) := by
  have h := indexed_simplified_basis_span (simplifiedBasisTuple A)
    (simplifiedBasisTuple_injective A) (simplifiedBasisTuple_rank A)
    (simplifiedBasisTuple_sup A) rfl
  exact ⟨fun S T ↦ (h.1 S T).2, h.2.1⟩

noncomputable def maximumAntichainTuple (C : MaximumBooleanAntichain M) :
    Fin (MatroidFlat.rank (⊤ : MatroidFlat M)) → MatroidFlat M :=
  fun i ↦ (canonicalEnumeration C i).1

lemma maximumAntichainTuple_boolean (C : MaximumBooleanAntichain M) :
    IsBooleanTuple (maximumAntichainTuple C) :=
  (isBooleanTuple_iff_antichain_of_equiv C.1 (canonicalEnumeration C)).mpr C.2.2

lemma maximumAntichainTuple_carrier (C : MaximumBooleanAntichain M) :
    orderedCarrier (maximumAntichainTuple C) = C.1 :=
  orderedCarrier_of_equiv C.1 (canonicalEnumeration C)

lemma maximumAntichainTuple_bottom (C : MaximumBooleanAntichain M) :
    commonMeet (maximumAntichainTuple C) = ⊥ :=
  full_height_commonMeet_eq_bot (maximumAntichainTuple_boolean C) rfl

/-- Phi is well defined, using full-height rigidity, not a rank-one premise. -/
theorem maximumAntichain_atoms_isSimplifiedBasis (C : MaximumBooleanAntichain M) :
    IsSimplifiedBasis M (antichainAtoms C.1) := by
  let H := maximumAntichainTuple C
  have hH : IsBooleanTuple H := maximumAntichainTuple_boolean C
  have hbot : commonMeet H = ⊥ := maximumAntichainTuple_bottom C
  rw [← maximumAntichainTuple_carrier C,
    antichainAtoms_orderedCarrier _ (isBooleanTuple_injective hH)]
  refine ⟨?_, ?_, ?_⟩
  · intro F hF
    rcases Finset.mem_image.mp hF with ⟨i, _, rfl⟩
    exact full_height_atom_grade hH rfl i
  · change (Finset.univ.image (reconstructedAtom H)).card = _
    rw [Finset.card_image_of_injective _ (reconstructedAtom_injective hH)]
    simp
  · change (Finset.univ.image (reconstructedAtom H)).sup id = ⊤
    rw [Finset.sup_image]
    exact reconstructedAtoms_sup_top hH hbot

/-- Psi is well defined, using the full basis-span producer. -/
theorem simplifiedBasis_coatoms_isMaximum (A : SimplifiedBasis M) :
    (basisCoatoms A.1).card = MatroidFlat.rank (⊤ : MatroidFlat M) ∧
      IsBooleanAntichain (basisCoatoms A.1) := by
  let a := simplifiedBasisTuple A
  have hspan := simplifiedBasisTuple_span A
  have hH : IsBooleanTuple (coatomTuple a) :=
    coatomTuple_isBoolean a (simplifiedBasisTuple_sup A) hspan.1 hspan.2
  rw [← simplifiedBasisTuple_carrier A,
    basisCoatoms_orderedCarrier _ (simplifiedBasisTuple_injective A)]
  exact ⟨orderedCarrier_card hH, orderedCarrier_isBoolean hH⟩

noncomputable def maximumAntichainToBasis (C : MaximumBooleanAntichain M) : SimplifiedBasis M :=
  ⟨antichainAtoms C.1, maximumAntichain_atoms_isSimplifiedBasis C⟩

noncomputable def simplifiedBasisToAntichain (A : SimplifiedBasis M) : MaximumBooleanAntichain M :=
  ⟨basisCoatoms A.1, simplifiedBasis_coatoms_isMaximum A⟩

theorem basisCoatoms_antichainAtoms (C : MaximumBooleanAntichain M) :
    basisCoatoms (antichainAtoms C.1) = C.1 := by
  let H := maximumAntichainTuple C
  have hH : IsBooleanTuple H := maximumAntichainTuple_boolean C
  have hbot : commonMeet H = ⊥ := maximumAntichainTuple_bottom C
  have hcarrier : orderedCarrier H = C.1 := maximumAntichainTuple_carrier C
  calc
    basisCoatoms (antichainAtoms C.1) =
        basisCoatoms (orderedCarrier (reconstructedAtom H)) := by
          rw [← hcarrier, antichainAtoms_orderedCarrier H (isBooleanTuple_injective hH)]
    _ = orderedCarrier (coatomTuple (reconstructedAtom H)) :=
      basisCoatoms_orderedCarrier _ (reconstructedAtom_injective hH)
    _ = orderedCarrier H := by rw [coatomTuple_reconstructedAtom hH hbot]
    _ = C.1 := hcarrier

theorem antichainAtoms_basisCoatoms (A : SimplifiedBasis M) :
    antichainAtoms (basisCoatoms A.1) = A.1 := by
  let a := simplifiedBasisTuple A
  have hspan := simplifiedBasisTuple_span A
  have htop := simplifiedBasisTuple_sup A
  have hH : IsBooleanTuple (coatomTuple a) := coatomTuple_isBoolean a htop hspan.1 hspan.2
  have hcarrier : orderedCarrier a = A.1 := simplifiedBasisTuple_carrier A
  calc
    antichainAtoms (basisCoatoms A.1) =
        antichainAtoms (orderedCarrier (coatomTuple a)) := by
          rw [← hcarrier, basisCoatoms_orderedCarrier a (simplifiedBasisTuple_injective A)]
    _ = orderedCarrier (reconstructedAtom (coatomTuple a)) :=
      antichainAtoms_orderedCarrier _ (isBooleanTuple_injective hH)
    _ = orderedCarrier a := by rw [reconstructedAtom_coatomTuple a htop hspan.1]
    _ = A.1 := hcarrier

/-- The exact unordered bijection Phi/Psi of `thm:main`. -/
noncomputable def maximumAntichainEquivSimplifiedBasis :
    MaximumBooleanAntichain M ≃ SimplifiedBasis M where
  toFun := maximumAntichainToBasis
  invFun := simplifiedBasisToAntichain
  left_inv C := Subtype.ext (basisCoatoms_antichainAtoms C)
  right_inv A := Subtype.ext (antichainAtoms_basisCoatoms A)

theorem maximumAntichain_count_eq_simplifiedBases :
    Fintype.card (MaximumBooleanAntichain M) = Fintype.card (SimplifiedBasis M) :=
  Fintype.card_congr maximumAntichainEquivSimplifiedBasis

end BooleanAntichainsKernel
