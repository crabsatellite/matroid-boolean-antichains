import BooleanAntichainsKernel.BasisChoices

namespace BooleanAntichainsKernel

open Set Finset
open scoped Classical

variable {α : Type*} [Fintype α] {M : Matroid α}

lemma basisChoice_unique_on_class (A : SimplifiedBasis M) (f : BasisClassChoice A)
    (F : A.1) {e : α} (he : e ∈ chosenBasisElements A f)
    (heF : e ∈ parallelClassElements F.1) : e = (f F).1 := by
  rcases Finset.mem_image.mp he with ⟨G, _, hGe⟩
  have hGF : G = F := by
    apply Subtype.ext
    calc
      G.1 = elementFlat M (f G).1 := (choice_elementFlat A f G).symm
      _ = elementFlat M e := congrArg (elementFlat M) hGe
      _ = F.1 := elementFlat_eq_of_parallelClass (A.2.1 F.1 F.2) heF
  subst G
  exact hGe.symm

theorem basisChoiceToBase_injective : Function.Injective (basisChoiceToBase (M := M)) := by
  rintro ⟨A, f⟩ ⟨B, g⟩ h
  have hvalues : chosenBasisElements A f = chosenBasisElements B g := congrArg Subtype.val h
  have hAB : A = B := by
    apply Subtype.ext
    calc
      A.1 = basisClassSet (M := M) (chosenBasisElements A f) := (chosenBasisElements_classes A f).symm
      _ = basisClassSet (M := M) (chosenBasisElements B g) := congrArg (basisClassSet (M := M)) hvalues
      _ = B.1 := chosenBasisElements_classes B g
  cases hAB
  apply congrArg (Sigma.mk A)
  funext F
  apply Subtype.ext
  have he : (f F).1 ∈ chosenBasisElements A g := by
    rw [← hvalues]
    exact Finset.mem_image.mpr ⟨F, mem_univ _, rfl⟩
  exact basisChoice_unique_on_class A g F he (f F).2

theorem basisChoiceToBase_surjective : Function.Surjective (basisChoiceToBase (M := M)) := by
  intro B
  let A := basisToSimplifiedBasis B
  have hchoose : ∀ F : A.1, ∃ e : parallelClassElements F.1, e.1 ∈ B.1 := by
    intro F
    have hF : F.1 ∈ B.1.image (elementFlat M) := F.2
    rcases Finset.mem_image.mp hF with ⟨e, heB, heF⟩
    have heClass : e ∈ parallelClassElements F.1 := by
      rw [← heF]
      exact basis_member_parallelClass B.2 heB
    exact ⟨⟨e, heClass⟩, heB⟩
  choose f hf using hchoose
  refine ⟨⟨A, f⟩, Subtype.ext ?_⟩
  change chosenBasisElements A f = B.1
  apply Finset.eq_of_subset_of_card_le
  · intro e he
    rcases Finset.mem_image.mp he with ⟨F, _, hFe⟩
    exact hFe ▸ hf F
  · rw [chosenBasisElements_card]
    exact (basisClassSet_card B.2).ge

/-- The actual basis partition used in `thm:weighted`. -/
noncomputable def basisChoicesEquivBases : BasisChoices M ≃ MatroidBases M :=
  Equiv.ofBijective basisChoiceToBase ⟨basisChoiceToBase_injective, basisChoiceToBase_surjective⟩

@[simp] lemma basisChoicesEquivBases_apply_val (x : BasisChoices M) :
    (basisChoicesEquivBases x).1 = chosenBasisElements x.1 x.2 := rfl

/-- The class family recovered from a chosen basis is exactly its sigma
index, so this is a partition by classes rather than just an equinumerosity. -/
lemma basisChoicesEquivBases_class_index (x : BasisChoices M) :
    basisToSimplifiedBasis (basisChoicesEquivBases x) = x.1 := by
  apply Subtype.ext
  exact chosenBasisElements_classes x.1 x.2

end BooleanAntichainsKernel
