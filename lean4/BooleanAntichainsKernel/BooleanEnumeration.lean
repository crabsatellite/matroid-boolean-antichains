import BooleanAntichainsKernel.BooleanTight
import BooleanAntichainsKernel.BooleanStirlingTransport

namespace BooleanAntichainsKernel

open Finset
open scoped Classical

/-- The complementary subtype of the same actual size-k Boolean antichains,
not a number defined by the desired difference formula. -/
abbrev BooleanLatticeNonRankTightAntichain (α : Type*) [Fintype α] (k : ℕ) :=
  {C : BooleanAntichain k (Finset α) // ¬(C.1.inf id).card = Fintype.card α - k}

noncomputable instance {α : Type*} [Fintype α] (k : ℕ) :
    Fintype (BooleanLatticeNonRankTightAntichain α k) := Subtype.fintype _

theorem booleanLattice_choose_le_stirling (n k : ℕ) :
    n.choose k ≤ Nat.stirlingSecond (n + 1) (k + 1) := by
  have h := Fintype.card_le_of_injective
    (fun C : BooleanLatticeRankTightAntichain (Fin n) k ↦ C.1) Subtype.val_injective
  simpa only [booleanLattice_rankTight_count, booleanLattice_count_stirling_general, Fintype.card_fin] using h

lemma booleanLattice_nonRankTight_count_eq_sub {α : Type*} [Fintype α] (k : ℕ) :
    Fintype.card (BooleanLatticeNonRankTightAntichain α k) =
      Fintype.card (BooleanAntichain k (Finset α)) -
        Fintype.card (BooleanLatticeRankTightAntichain α k) :=
  @Fintype.card_subtype_compl (BooleanAntichain k (Finset α)) _
    (fun C ↦ (C.1.inf id).card = Fintype.card α - k)
    (inferInstance : Fintype (BooleanLatticeRankTightAntichain α k))
    (inferInstance : Fintype (BooleanLatticeNonRankTightAntichain α k))

theorem booleanLattice_nonRankTight_count (n k : ℕ) :
    Fintype.card (BooleanLatticeNonRankTightAntichain (Fin n) k) =
      Nat.stirlingSecond (n + 1) (k + 1) - n.choose k := by
  rw [booleanLattice_nonRankTight_count_eq_sub,
    @booleanLattice_count_stirling_general (Fin n) _ (Classical.decEq _) k,
    booleanLattice_rankTight_count, Fintype.card_fin]

/-- All three count assertions in the Boolean-lattice corollary. -/
theorem booleanLattice_enumeration (n k : ℕ) :
    Fintype.card (BooleanLatticeRankTightAntichain (Fin n) k) = n.choose k ∧
    Fintype.card (BooleanAntichain k (Finset (Fin n))) = Nat.stirlingSecond (n + 1) (k + 1) ∧
    Fintype.card (BooleanLatticeNonRankTightAntichain (Fin n) k) =
      Nat.stirlingSecond (n + 1) (k + 1) - n.choose k := by
  exact ⟨by simpa using booleanLattice_rankTight_count (α := Fin n) k,
    booleanLattice_count_stirling n k, booleanLattice_nonRankTight_count n k⟩

end BooleanAntichainsKernel
