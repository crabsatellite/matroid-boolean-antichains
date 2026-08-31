import BooleanAntichainsKernel.BasisChoiceBijection

/-! Expand the actual basis partition into products of parallel-class sums.
This is proved over an arbitrary commutative semiring, then specialized to
the symbolic multivariate polynomial and to natural-number counting. -/

namespace BooleanAntichainsKernel

open Set Finset
open scoped Classical

variable {α R : Type*} [Fintype α] {M : Matroid α}

lemma prod_chosenBasisElements [CommMonoid R] (A : SimplifiedBasis M)
    (f : BasisClassChoice A) (x : α → R) :
    (∏ e ∈ chosenBasisElements A f, x e) = ∏ F : A.1, x (f F).1 := by
  rw [chosenBasisElements, Finset.prod_image (basisChoice_injective A f).injOn]

lemma sum_basisClassChoice_products [CommSemiring R] (A : SimplifiedBasis M) (x : α → R) :
    (∑ f : BasisClassChoice A, ∏ F : A.1, x (f F).1) =
      ∏ F ∈ A.1, ∑ e ∈ parallelClassElements F, x e := by
  have h := (Fintype.prod_sum (fun (F : A.1) (e : parallelClassElements F.1) ↦ x e.1)).symm
  calc
    _ = ∏ F : A.1, ∑ e : parallelClassElements F.1, x e.1 := h
    _ = ∏ F : A.1, ∑ e ∈ parallelClassElements F.1, x e := by
      simp only [Finset.sum_coe_sort]
    _ = ∏ F ∈ A.1, ∑ e ∈ parallelClassElements F, x e :=
      Finset.prod_coe_sort A.1 (fun F ↦ ∑ e ∈ parallelClassElements F, x e)

theorem basisWeight_sum_parallel_classes [CommSemiring R] (M : Matroid α) (x : α → R) :
    (∑ B : MatroidBases M, ∏ e ∈ B.1, x e) =
      ∑ A : SimplifiedBasis M, ∏ F ∈ A.1, ∑ e ∈ parallelClassElements F, x e := by
  calc
    _ = ∑ t : BasisChoices M, ∏ e ∈ chosenBasisElements t.1 t.2, x e :=
      (basisChoicesEquivBases.sum_comp (fun B : MatroidBases M ↦ ∏ e ∈ B.1, x e)).symm
    _ = ∑ A : SimplifiedBasis M, ∑ f : BasisClassChoice A,
        ∏ e ∈ chosenBasisElements A f, x e :=
      Fintype.sum_sigma' (fun (A : SimplifiedBasis M) (f : BasisClassChoice A) ↦
        ∏ e ∈ chosenBasisElements A f, x e)
    _ = ∑ A : SimplifiedBasis M, ∏ F ∈ A.1, ∑ e ∈ parallelClassElements F, x e := by
      apply Finset.sum_congr rfl
      intro A _
      simp_rw [prod_chosenBasisElements]
      exact sum_basisClassChoice_products A x

/-- Consume the actual maximum-antichain bijection to return to the paper's
indexing family. The equality with the literal span atoms is proved next. -/
theorem basisWeight_sum_maximum_antichains [CommSemiring R] (M : Matroid α) (x : α → R) :
    (∑ B : MatroidBases M, ∏ e ∈ B.1, x e) =
      ∑ C : MaximumBooleanAntichain M,
        ∏ F ∈ antichainAtoms C.1, ∑ e ∈ parallelClassElements F, x e := by
  rw [basisWeight_sum_parallel_classes]
  exact (maximumAntichainEquivSimplifiedBasis.sum_comp
    (fun A : SimplifiedBasis M ↦ ∏ F ∈ A.1, ∑ e ∈ parallelClassElements F, x e)).symm

/-- The literal basis generating polynomial, with one monomial per actual
matroid basis. This definition does not use the desired decomposition. -/
noncomputable def matroidBasisPolynomial (M : Matroid α) : MvPolynomial α ℤ :=
  ∑ B : MatroidBases M, ∏ e ∈ B.1, MvPolynomial.X e

theorem basis_polynomial_reconstructed_atoms (M : Matroid α) :
    matroidBasisPolynomial M =
      ∑ C : MaximumBooleanAntichain M,
        ∏ F ∈ antichainAtoms C.1, ∑ e ∈ parallelClassElements F,
          (MvPolynomial.X e : MvPolynomial α ℤ) :=
  basisWeight_sum_maximum_antichains M MvPolynomial.X

theorem basis_count_reconstructed_atoms (M : Matroid α) :
    Fintype.card (MatroidBases M) =
      ∑ C : MaximumBooleanAntichain M,
        ∏ F ∈ antichainAtoms C.1, (parallelClassElements F).card := by
  simpa using basisWeight_sum_maximum_antichains M (fun _ : α ↦ (1 : ℕ))

end BooleanAntichainsKernel
