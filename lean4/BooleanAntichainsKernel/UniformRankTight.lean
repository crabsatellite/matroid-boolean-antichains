import BooleanAntichainsKernel.UniformSimplification
import BooleanAntichainsKernel.UniformCorank

namespace BooleanAntichainsKernel

open Set Finset
open scoped Classical Matroid

variable {α : Type*} [Fintype α]

/-- The exact uniform minor and remaining ground size at a corank-k flat. -/
theorem uniformOn_contract_corank (E : Set α) (r : ℕ) (hr : r ≤ E.ncard)
    (k : ℕ) (hk : 0 < k) (X : CorankFlat (uniformOn E r) k) :
    (uniformOn E r) ／ X.1.1 = uniformOn (E \ X.1.1) k ∧
    (E \ X.1.1).ncard = E.ncard - (r - k) ∧ k ≤ (E \ X.1.1).ncard := by
  have hs := (uniformOn_hasCorank_iff E r hr k hk X.1).mp X.2
  have hXE : X.1.1 ⊆ E := X.1.2.subset_ground
  refine ⟨?_, ?_, ?_⟩
  · rw [uniformOn_contract E r X.1.1 hXE (by omega), show r - X.1.1.ncard = k by omega]
  · rw [Set.ncard_sdiff hXE, show X.1.1.ncard = r - k by omega]
  · rw [Set.ncard_sdiff hXE]
    omega

lemma uniformOn_corank_contraction_simplifiedBasis_count (E : Set α) (r : ℕ)
    (hr : r ≤ E.ncard) (k : ℕ) (hk : 0 < k) (X : CorankFlat (uniformOn E r) k) :
    Fintype.card (SimplifiedBasis ((uniformOn E r) ／ X.1.1)) =
      if k = 1 then 1 else (E.ncard - (r - k)).choose k := by
  obtain ⟨hminor, hsize, hbound⟩ := uniformOn_contract_corank E r hr k hk X
  rw [hminor]
  by_cases hk1 : k = 1
  · subst k
    rw [if_pos rfl]
    exact uniformOn_rank_one_simplifiedBasis_count _ hbound
  · rw [if_neg hk1, uniformOn_simplifiedBasis_count _ k (by omega) hbound, hsize]

lemma uniform_binomial_normalization (n r k : ℕ) (hk : k ≤ r) :
    n.choose (r - k) * (n - (r - k)).choose k = n.choose r * r.choose k := by
  have h := Nat.choose_mul (n := n) (k := r) (s := r - k) (Nat.sub_le r k)
  rw [Nat.choose_symm hk, Nat.sub_sub_self hk] at h
  exact h.symm

/-- Consume the literal corank-flat sum, retaining the rank-one
simplification exception and the positive-rank boundary. -/
theorem uniformOn_rankTight_count_positive (E : Set α) (r : ℕ) (hr : r ≤ E.ncard)
    (k : ℕ) (hk : 0 < k) (hkr : k ≤ r) :
    Fintype.card (RankTightAntichain (uniformOn E r) k) =
      if k = 1 then E.ncard.choose (r - 1) else E.ncard.choose r * r.choose k := by
  rw [rankTight_count_by_bottom_subtype]
  simp_rw [uniformOn_corank_contraction_simplifiedBasis_count E r hr k hk]
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [uniformOn_corankFlat_count E r hr k hk hkr]
  by_cases hk1 : k = 1
  · subst k
    simp
  · simp only [if_neg hk1]
    exact uniform_binomial_normalization E.ncard r k hkr

/-- The full displayed uniform rank-tight corollary, including the zero and
rank-one branches, on the actual uniform matroid with ground Fin n. -/
theorem uniform_rankTight_enumeration (n r : ℕ) (hr2 : 2 ≤ r) (hrn : r ≤ n) :
    Fintype.card (RankTightAntichain (uniformOn (Set.univ : Set (Fin n)) r) 0) = 1 ∧
    Fintype.card (RankTightAntichain (uniformOn (Set.univ : Set (Fin n)) r) 1) =
      n.choose (r - 1) ∧
    (∀ k : ℕ, 2 ≤ k → k ≤ r →
      Fintype.card (RankTightAntichain (uniformOn (Set.univ : Set (Fin n)) r) k) =
        n.choose r * r.choose k) ∧
    (∀ k : ℕ, r < k →
      Fintype.card (RankTightAntichain (uniformOn (Set.univ : Set (Fin n)) r) k) = 0) := by
  have hrE : r ≤ (Set.univ : Set (Fin n)).ncard := by
    simpa only [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] using hrn
  refine ⟨rankTight_count_zero _, ?_, ?_, ?_⟩
  · simpa only [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin, if_true] using
      uniformOn_rankTight_count_positive (Set.univ : Set (Fin n)) r hrE 1 (by omega) (by omega)
  · intro k hk2 hkr
    simpa only [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin,
      if_neg (show k ≠ 1 by omega)] using
      uniformOn_rankTight_count_positive (Set.univ : Set (Fin n)) r hrE k (by omega) hkr
  · intro k hk
    apply rankTight_count_above_rank
    change matroidRank (uniformOn (Set.univ : Set (Fin n)) r) Set.univ < k
    rw [uniformOn_ground_rank _ r hrE]
    exact hk

end BooleanAntichainsKernel
