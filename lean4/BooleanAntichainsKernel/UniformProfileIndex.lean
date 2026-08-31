import BooleanAntichainsKernel.UniformBlockProfiles
import BooleanAntichainsKernel.UniformSingletonCounting
import BooleanAntichainsKernel.SizedBlockCoefficients
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace BooleanAntichainsKernel

open Finset
open scoped Classical

/-- The paper's natural-number profile variables, with their exact
constraints. Bounded codes are used only to prove this carrier is finite. -/
abbrev UniformAdmissibleProfile (n r k b : ℕ) :=
  {p : Fin k → ℕ // UniformProfileValid n r k b p}

lemma uniformAdmissibleProfile_le {n r k b : ℕ} (p : UniformAdmissibleProfile n r k b) (i : Fin k) :
    p.1 i ≤ n := by
  have hi : p.1 i ≤ ∑ j, p.1 j :=
    Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
  exact hi.trans (p.2.2.2.1.trans (Nat.sub_le n b))

def uniformProfileBoundedCode {n r k b : ℕ} (p : UniformAdmissibleProfile n r k b) :
    Fin k → Fin (n + 1) := fun i ↦ ⟨p.1 i, Nat.lt_succ_of_le (uniformAdmissibleProfile_le p i)⟩

lemma uniformProfileBoundedCode_injective {n r k b : ℕ} :
    Function.Injective (uniformProfileBoundedCode (n := n) (r := r) (k := k) (b := b)) := by
  intro p q h
  apply Subtype.ext
  funext i
  exact congrArg Fin.val (congrFun h i)

noncomputable instance (n r k b : ℕ) : Fintype (UniformAdmissibleProfile n r k b) :=
  Fintype.ofInjective uniformProfileBoundedCode uniformProfileBoundedCode_injective

variable {α : Type*} [Fintype α]

/-- The literal remaining ground E minus the actual chosen bottom. -/
noncomputable def blockAvailableGround (E : Set α) (X : Finset α) : Finset α :=
  (E \ (X : Set α)).toFinset

@[simp] lemma mem_blockAvailableGround (E : Set α) (X : Finset α) (e : α) :
    e ∈ blockAvailableGround E X ↔ e ∈ E ∧ e ∉ X := by
  simp [blockAvailableGround]

theorem blockAvailableGround_card (E : Set α) (X : Finset α) (hXE : (X : Set α) ⊆ E) :
    (blockAvailableGround E X).card = E.ncard - X.card := by
  rw [blockAvailableGround, ← Set.ncard_eq_toFinset_card', Set.ncard_sdiff hXE, Set.ncard_coe_finset]

theorem fixedBottom_blocks_count (E : Set α) (X : Finset α) (hXE : (X : Set α) ⊆ E)
    {k : ℕ} (p : Fin k → ℕ) (hp : (∑ i, p i) ≤ E.ncard - X.card) :
    Fintype.card (SizedDisjointBlocks (blockAvailableGround E X) p) =
      (E.ncard - X.card).factorial /
        ((E.ncard - X.card - ∑ i, p i).factorial * ∏ i, (p i).factorial) := by
  have hbound : (∑ i, p i) ≤ (blockAvailableGround E X).card := by
    rwa [blockAvailableGround_card E X hXE]
  rw [sizedDisjointBlocks_count hbound, blockAvailableGround_card E X hXE]

/-- Actual bottom, an admissible natural-number profile, and an actual
disjoint family on the remaining ground. No cardinality is defined by a formula. -/
abbrev UniformBlockDecomposition (E : Set α) (r k : ℕ) :=
  Σ X : SmallGroundSubsets E r,
    Σ p : UniformAdmissibleProfile E.ncard r k X.1.card,
      SizedDisjointBlocks (blockAvailableGround E X.1) p.1

end BooleanAntichainsKernel
