import BooleanAntichainsKernel.HomEnumeration

/-! Exact active-cover multiplicities in the proof of the product law. -/

namespace BooleanAntichainsKernel

open Finset
open scoped Classical

/-- Missing labels of the second active set are precisely a subset of the
first active set. This counts actual covering pairs, not a surrogate. -/
def coveringPartnerEquivPowersetCard {k b : ℕ} (A : Finset (Fin k)) (hb : b ≤ k) :
    {B : Finset (Fin k) // B.card = b ∧ A ∪ B = univ} ≃
      ↥(A.powersetCard (k - b)) where
  toFun B := ⟨univ \ B.1, by
    apply Finset.mem_powersetCard.mpr
    constructor
    · intro i hi
      have hnot := (Finset.mem_sdiff.mp hi).2
      have hmem : i ∈ A ∪ B.1 := B.2.2.symm ▸ Finset.mem_univ i
      exact (Finset.mem_union.mp hmem).resolve_right hnot
    · rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
      simp [B.2.1]⟩
  invFun D := ⟨univ \ D.1, by
    have hD := Finset.mem_powersetCard.mp D.2
    constructor
    · rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
      simp only [Finset.card_univ, Fintype.card_fin, hD.2]
      omega
    · apply Finset.eq_univ_of_forall
      intro i
      by_cases hi : i ∈ D.1
      · exact Finset.mem_union_left _ (hD.1 hi)
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hi⟩)⟩
  left_inv B := Subtype.ext (Finset.sdiff_sdiff_eq_self (Finset.subset_univ B.1))
  right_inv D := Subtype.ext (Finset.sdiff_sdiff_eq_self (Finset.subset_univ D.1))

theorem card_covering_partners {k b : ℕ} (A : Finset (Fin k)) (hb : b ≤ k) :
    Fintype.card {B : Finset (Fin k) // B.card = b ∧ A ∪ B = univ} =
      A.card.choose (k - b) := by
  rw [Fintype.card_congr (coveringPartnerEquivPowersetCard A hb), Fintype.card_coe,
    Finset.card_powersetCard]

/-- Group the actual second active sets by their cardinalities. -/
theorem sum_covering_partners_by_card {k : ℕ} (A : Finset (Fin k)) (w : ℕ → ℕ) :
    (∑ B : Finset (Fin k), if A ∪ B = univ then w B.card else 0) =
      ∑ b ∈ Finset.range (k + 1), A.card.choose (k - b) * w b := by
  let U : Finset (Finset (Fin k)) := univ
  have hmap : ∀ B ∈ U, B.card ∈ Finset.range (k + 1) := by
    intro B _
    apply Finset.mem_range.mpr
    have hc : B.card ≤ k := by simpa using Finset.card_le_card (Finset.subset_univ B)
    omega
  calc
    _ = ∑ b ∈ Finset.range (k + 1),
        ∑ B ∈ U.filter (fun B ↦ B.card = b), if A ∪ B = univ then w B.card else 0 :=
      (Finset.sum_fiberwise_of_maps_to (s := U) (t := Finset.range (k + 1))
        (g := Finset.card) hmap (fun B ↦ if A ∪ B = univ then w B.card else 0)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro b hb
      have hcount := card_covering_partners A (Nat.le_of_lt_succ (Finset.mem_range.mp hb))
      rw [Fintype.card_subtype] at hcount
      calc
        _ = ∑ B ∈ U.filter (fun B ↦ B.card = b), if A ∪ B = univ then w b else 0 := by
          apply Finset.sum_congr rfl
          intro B hB
          rw [(Finset.mem_filter.mp hB).2]
        _ = (U.filter (fun B ↦ B.card = b ∧ A ∪ B = univ)).card * w b := by
          rw [← Finset.sum_filter]
          simp [Finset.filter_filter]
        _ = A.card.choose (k - b) * w b := by rw [show
          (U.filter (fun B ↦ B.card = b ∧ A ∪ B = univ)).card = A.card.choose (k - b) from hcount]

end BooleanAntichainsKernel
