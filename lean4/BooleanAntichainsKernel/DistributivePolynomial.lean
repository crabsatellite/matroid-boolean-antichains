import BooleanAntichainsKernel.FilterIntersectionGraph
import Mathlib.Algebra.Polynomial.Coeff

namespace BooleanAntichainsKernel

open Finset
open scoped Classical

/-- The ordinary size-enumerating polynomial of a finite family of subsets. -/
noncomputable def finiteFamilyPolynomial {V : Type*} [Fintype V]
    (p : Finset V → Prop) : Polynomial ℕ :=
  ∑ S : Finset V, if p S then Polynomial.X ^ S.card else 0

lemma finiteFamilyPolynomial_coeff {V : Type*} [Fintype V]
    (p : Finset V → Prop) (k : ℕ) :
    (finiteFamilyPolynomial p).coeff k = Fintype.card {S : Finset V // S.card = k ∧ p S} := by
  rw [finiteFamilyPolynomial, Polynomial.finsetSum_coeff]
  calc
    _ = ∑ S : Finset V, if S.card = k ∧ p S then (1 : ℕ) else 0 := by
      apply Finset.sum_congr rfl
      intro S _
      by_cases hp : p S
      · by_cases hk : S.card = k
        · simp [hp, hk]
        · have hk' : k ≠ S.card := Ne.symm hk
          simp [hp, hk, hk', Polynomial.coeff_X_pow]
      · simp [hp]
    _ = Fintype.card {S : Finset V // S.card = k ∧ p S} := by
      rw [Finset.sum_boole, Fintype.card_subtype]
      simp

/-- The actual independence polynomial, formed by summing `X^|S|` over the
independent vertex sets of a `SimpleGraph`. -/
noncomputable def graphIndependencePolynomial {V : Type*} [Fintype V]
    (G : SimpleGraph V) : Polynomial ℕ :=
  finiteFamilyPolynomial (fun S : Finset V ↦ G.IsIndepSet (S : Set V))

lemma graphIndependencePolynomial_coeff {V : Type*} [Fintype V]
    (G : SimpleGraph V) (k : ℕ) :
    (graphIndependencePolynomial G).coeff k = Fintype.card (GraphIndependentFamily G k) := by
  rw [graphIndependencePolynomial, finiteFamilyPolynomial_coeff]
  exact congrArg (@Fintype.card (GraphIndependentFamily G k)) (Subsingleton.elim _ _)

/-- The left-hand generating polynomial in `thm:distributive`, on literal unordered
antichains rather than a formula taken as their definition. -/
noncomputable def booleanAntichainPolynomial (L : Type*) [Fintype L] [DecidableEq L]
    [Lattice L] [OrderBot L] [OrderTop L] : Polynomial ℕ :=
  finiteFamilyPolynomial (IsBooleanAntichain (L := L))

lemma booleanAntichainPolynomial_coeff (L : Type*) [Fintype L] [DecidableEq L]
    [Lattice L] [OrderBot L] [OrderTop L] (k : ℕ) :
    (booleanAntichainPolynomial L).coeff k = Fintype.card (BooleanAntichain k L) :=
  finiteFamilyPolynomial_coeff _ k

/-- The displayed polynomial identity of `thm:distributive`. -/
theorem distributive_polynomial_identity (P : Type*) [PartialOrder P] [Fintype P] :
    booleanAntichainPolynomial (LowerSet P) = graphIndependencePolynomial (filterIntersectionGraph P) := by
  ext k
  rw [booleanAntichainPolynomial_coeff, graphIndependencePolynomial_coeff]
  exact distributive_count_eq_graph_independent k

/-- The previously constructed coefficient is now bound to the coefficient
of the literal graph independence polynomial. -/
theorem filterIntersectionIndependenceCoeff_eq_graph_coeff (P : Type*) [PartialOrder P]
    [Fintype P] (k : ℕ) :
    filterIntersectionIndependenceCoeff (P := P) k =
      (graphIndependencePolynomial (filterIntersectionGraph P)).coeff k := by
  rw [graphIndependencePolynomial_coeff]
  exact Fintype.card_congr (disjointFiltersEquivGraphIndependent k)

end BooleanAntichainsKernel
