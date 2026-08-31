import BooleanAntichainsKernel.UniformProfileAssembly
import BooleanAntichainsKernel.UniformBlockBijection

namespace BooleanAntichainsKernel

open Finset
open scoped Classical

variable {α : Type*} [Fintype α]

theorem sum_smallGroundSubsets_by_card (E : Set α) (r : ℕ) (w : ℕ → ℕ) :
    (∑ X : SmallGroundSubsets E r, w X.1.card) =
      ∑ b ∈ Finset.range r, E.ncard.choose b * w b := by
  calc
    _ = ∑ Y : Σ b : Fin r, ↥(E.toFinset.powersetCard b.1), w Y.1.1 :=
      Fintype.sum_equiv (smallGroundSubsetsEquivSigma E r) _ _ (fun _ ↦ rfl)
    _ = ∑ b : Fin r, E.ncard.choose b.1 * w b.1 := by
      simp only [Fintype.sum_sigma, Finset.sum_const, Finset.card_univ, smul_eq_mul,
        Fintype.card_coe, Finset.card_powersetCard, ← Set.ncard_eq_toFinset_card']
    _ = _ := Fin.sum_univ_eq_sum_range (fun b ↦ E.ncard.choose b * w b) r

variable [DecidableEq α]

theorem uniformBlockData_count_by_bottom_profile (E : Set α) (r k : ℕ) :
    Fintype.card (UniformBlockData E r k) =
      ∑ X : SmallGroundSubsets E r,
        ∑ p : UniformAdmissibleProfile E.ncard r k X.1.card,
          (E.ncard - X.1.card).factorial /
            ((E.ncard - X.1.card - ∑ i, p.1 i).factorial * ∏ i, (p.1 i).factorial) := by
  calc
    _ = Fintype.card (UniformBlockDecomposition E r k) :=
      (Fintype.card_congr uniformProfileDecompositionEquiv).symm
    _ = ∑ X : SmallGroundSubsets E r,
        ∑ p : UniformAdmissibleProfile E.ncard r k X.1.card,
          Fintype.card (SizedDisjointBlocks (blockAvailableGround E X.1) p.1) := by
      simp only [Fintype.card_sigma]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro X _
      apply Finset.sum_congr rfl
      intro p _
      exact fixedBottom_blocks_count E X.1
        (fun e he ↦ Set.mem_toFinset.mp (X.2.1 he)) p.1 p.2.2.2.1

theorem uniformBlockData_count_by_profile (E : Set α) (r k : ℕ) :
    Fintype.card (UniformBlockData E r k) =
      ∑ b ∈ Finset.range r, E.ncard.choose b *
        ∑ p : UniformAdmissibleProfile E.ncard r k b,
          (E.ncard - b).factorial /
            ((E.ncard - b - ∑ i, p.1 i).factorial * ∏ i, (p.1 i).factorial) := by
  rw [uniformBlockData_count_by_bottom_profile]
  exact sum_smallGroundSubsets_by_card E r (fun b ↦
    ∑ p : UniformAdmissibleProfile E.ncard r k b,
      (E.ncard - b).factorial /
        ((E.ncard - b - ∑ i, p.1 i).factorial * ∏ i, (p.1 i).factorial))

/-- The full displayed constrained block sum. Both divisions are earned
from actual finite fibres; no floor operation is used as a surrogate count. -/
theorem uniformOn_all_size_formula (E : Set α) (r k : ℕ)
    (hr : r ≤ E.ncard) (hk : 2 ≤ k) :
    Fintype.card (BooleanAntichain k (MatroidFlat (uniformOn E r))) =
      (∑ b ∈ Finset.range r, E.ncard.choose b *
        ∑ p : UniformAdmissibleProfile E.ncard r k b,
          (E.ncard - b).factorial /
            ((E.ncard - b - ∑ i, p.1 i).factorial * ∏ i, (p.1 i).factorial)) / k.factorial := by
  rw [uniformAntichain_count_blocks hr hk, uniformBlockData_count_by_profile]

theorem uniform_all_size_formula (n r k : ℕ) (hr : r ≤ n) (hk : 2 ≤ k) :
    Fintype.card (BooleanAntichain k (MatroidFlat (uniformOn (Set.univ : Set (Fin n)) r))) =
      (∑ b ∈ Finset.range r, n.choose b *
        ∑ p : UniformAdmissibleProfile n r k b,
          (n - b).factorial /
            ((n - b - ∑ i, p.1 i).factorial * ∏ i, (p.1 i).factorial)) / k.factorial := by
  have hrE : r ≤ (Set.univ : Set (Fin n)).ncard := by
    simpa only [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] using hr
  let F (N : ℕ) :=
    (∑ b ∈ Finset.range r, N.choose b *
      ∑ p : UniformAdmissibleProfile N r k b,
        (N - b).factorial /
          ((N - b - ∑ i, p.1 i).factorial * ∏ i, (p.1 i).factorial)) / k.factorial
  have hN : (Set.univ : Set (Fin n)).ncard = n := by
    simp only [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
  have h := uniformOn_all_size_formula (Set.univ : Set (Fin n)) r k hrE hk
  change Fintype.card (BooleanAntichain k (MatroidFlat (uniformOn (Set.univ : Set (Fin n)) r))) =
    F (Set.univ : Set (Fin n)).ncard at h
  exact h.trans (congrArg F hN)

end BooleanAntichainsKernel
