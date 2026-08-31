import BooleanAntichainsKernel.ParallelClasses

namespace BooleanAntichainsKernel

open Set Finset
open scoped Classical

variable {α : Type*} [Fintype α] {M : Matroid α}

/-- One genuine nonloop element in each parallel class of a simplified basis. -/
abbrev BasisClassChoice (A : SimplifiedBasis M) :=
  (F : A.1) → parallelClassElements F.1

noncomputable def chosenBasisElements (A : SimplifiedBasis M) (f : BasisClassChoice A) : Finset α :=
  Finset.univ.image (fun F : A.1 ↦ (f F).1)

lemma choice_elementFlat (A : SimplifiedBasis M) (f : BasisClassChoice A) (F : A.1) :
    elementFlat M (f F).1 = F.1 :=
  elementFlat_eq_of_parallelClass (A.2.1 F.1 F.2) (f F).2

lemma basisChoice_injective (A : SimplifiedBasis M) (f : BasisClassChoice A) :
    Function.Injective (fun F : A.1 ↦ (f F).1) := by
  intro F G hFG
  apply Subtype.ext
  calc
    F.1 = elementFlat M (f F).1 := (choice_elementFlat A f F).symm
    _ = elementFlat M (f G).1 := congrArg (elementFlat M) hFG
    _ = G.1 := choice_elementFlat A f G

lemma chosenBasisElements_card (A : SimplifiedBasis M) (f : BasisClassChoice A) :
    (chosenBasisElements A f).card = A.1.card := by
  rw [chosenBasisElements, Finset.card_image_of_injective _ (basisChoice_injective A f)]
  simp

lemma chosenBasisElements_classes (A : SimplifiedBasis M) (f : BasisClassChoice A) :
    basisClassSet (M := M) (chosenBasisElements A f) = A.1 := by
  unfold basisClassSet chosenBasisElements
  rw [Finset.image_image]
  calc
    _ = (Finset.univ : Finset A.1).image Subtype.val := by
      apply Finset.image_congr
      intro F _
      exact choice_elementFlat A f F
    _ = A.1 := by
      ext F
      constructor
      · rintro hF
        rcases Finset.mem_image.mp hF with ⟨q, _, rfl⟩
        exact q.2
      · intro hF
        exact Finset.mem_image.mpr ⟨⟨F, hF⟩, mem_univ _, rfl⟩

theorem chosenBasisElements_isBase (A : SimplifiedBasis M) (f : BasisClassChoice A) :
    M.IsBase (chosenBasisElements A f : Set α) := by
  let e := simplifiedBasisEnumeration A
  let a := simplifiedBasisTuple A
  let g : Fin (MatroidFlat.rank (⊤ : MatroidFlat M)) → α := fun i ↦ (f (e i)).1
  have hg : ∀ i, M.closure {g i} = (a i).1 := by
    intro i
    exact congrArg Subtype.val (choice_elementFlat A f (e i))
  have hb : M.IsBase (Set.range g) := rank_one_representatives_isBase a
    (simplifiedBasisTuple_injective A) g hg (simplifiedBasisTuple_sup A) rfl
  have hset : Set.range g = (chosenBasisElements A f : Set α) := by
    ext x
    constructor
    · rintro ⟨i, hi⟩
      exact Finset.mem_image.mpr ⟨e i, mem_univ _, hi⟩
    · intro hx
      rcases Finset.mem_image.mp hx with ⟨F, _, hF⟩
      obtain ⟨i, hi⟩ := e.surjective F
      refine ⟨i, ?_⟩
      change (f (e i)).1 = x
      rw [hi]
      exact hF
  exact hset ▸ hb

abbrev BasisChoices (M : Matroid α) := Σ A : SimplifiedBasis M, BasisClassChoice A

noncomputable def basisChoiceToBase (x : BasisChoices M) : MatroidBases M :=
  ⟨chosenBasisElements x.1 x.2, chosenBasisElements_isBase x.1 x.2⟩

end BooleanAntichainsKernel
