import BooleanAntichainsKernel.UniformMatroid

namespace BooleanAntichainsKernel

open Set
open scoped Classical

variable {α : Type*} [Fintype α]

theorem uniformOn_closure_of_card_lt (E : Set α) (r : ℕ) (X : Set α)
    (hXE : X ⊆ E) (hcard : X.ncard < r) :
    (uniformOn E r).closure X = X := by
  have hI : (uniformOn E r).Indep X := (uniformOn_indep_iff E r X).mpr ⟨hXE, hcard.le⟩
  apply Set.Subset.antisymm ?_ ((uniformOn E r).subset_closure X hXE)
  intro e he
  have heE : e ∈ (uniformOn E r).E := (uniformOn E r).closure_subset_ground X he
  by_contra heX
  have hi : (uniformOn E r).Indep (insert e X) := by
    apply (uniformOn_indep_iff E r _).mpr
    refine ⟨Set.insert_subset_iff.mpr ⟨heE, hXE⟩, ?_⟩
    rw [Set.ncard_insert_of_notMem heX]
    omega
  exact ((hI.notMem_closure_iff_of_notMem heX heE).mpr hi) he

theorem uniformOn_closure_of_rank_le (E : Set α) (r : ℕ) (X : Set α)
    (hXE : X ⊆ E) (hcard : r ≤ X.ncard) :
    (uniformOn E r).closure X = E := by
  obtain ⟨B, hBX, hBr⟩ := Set.exists_subset_card_eq hcard
  have hrE : r ≤ E.ncard := hcard.trans (Set.ncard_le_ncard hXE)
  have hB : (uniformOn E r).IsBase B :=
    (uniformOn_isBase_iff E r hrE B).mpr ⟨hBX.trans hXE, hBr⟩
  apply Set.Subset.antisymm ((uniformOn E r).closure_subset_ground X)
  rw [← hB.closure_eq]
  exact (uniformOn E r).closure_subset_closure hBX

/-- Actual uniform closure, with no alternative flat-lattice model. -/
theorem uniformOn_closure (E : Set α) (r : ℕ) (X : Set α) (hXE : X ⊆ E) :
    (uniformOn E r).closure X = if X.ncard < r then X else E := by
  by_cases hcard : X.ncard < r
  · rw [if_pos hcard]
    exact uniformOn_closure_of_card_lt E r X hXE hcard
  · rw [if_neg hcard]
    exact uniformOn_closure_of_rank_le E r X hXE (Nat.le_of_not_gt hcard)

theorem uniformOn_isFlat_iff (E : Set α) (r : ℕ) (X : Set α) :
    (uniformOn E r).IsFlat X ↔ X ⊆ E ∧ (X.ncard < r ∨ X = E) := by
  constructor
  · intro hX
    refine ⟨hX.subset_ground, ?_⟩
    by_cases hsmall : X.ncard < r
    · exact Or.inl hsmall
    · exact Or.inr (hX.closure.symm.trans
        (uniformOn_closure_of_rank_le E r X hX.subset_ground (Nat.le_of_not_gt hsmall)))
  · rintro ⟨hXE, hsmall | hEq⟩
    · exact Matroid.isFlat_iff_closure_eq.mpr (uniformOn_closure_of_card_lt E r X hXE hsmall)
    · subst X
      exact (uniformOn E r).ground_isFlat

/-- The exact proper-flat statement used at the start of thm:uniform-all. -/
theorem uniformOn_properFlat_iff (E : Set α) (r : ℕ) (hr : r ≤ E.ncard) (X : Set α) :
    ((uniformOn E r).IsFlat X ∧ X ≠ E) ↔ X ⊆ E ∧ X.ncard < r := by
  constructor
  · rintro ⟨hX, hne⟩
    have h := (uniformOn_isFlat_iff E r X).mp hX
    exact ⟨h.1, h.2.resolve_right hne⟩
  · rintro ⟨hXE, hcard⟩
    refine ⟨(uniformOn_isFlat_iff E r X).mpr ⟨hXE, Or.inl hcard⟩, ?_⟩
    intro h
    rw [h] at hcard
    omega

theorem uniformOn_rank (E : Set α) (r : ℕ) (X : Set α) (hXE : X ⊆ E) :
    matroidRank (uniformOn E r) X = min r X.ncard := by
  by_cases hsmall : X.ncard < r
  · rw [matroidRank_indep ((uniformOn_indep_iff E r X).mpr ⟨hXE, hsmall.le⟩),
      Nat.min_eq_right hsmall.le]
  · have hrX : r ≤ X.ncard := Nat.le_of_not_gt hsmall
    rw [← matroidRank_closure (uniformOn E r) X, uniformOn_closure_of_rank_le E r X hXE hrX,
      uniformOn_ground_rank E r (hrX.trans (Set.ncard_le_ncard hXE)), Nat.min_eq_left hrX]

end BooleanAntichainsKernel
