import BooleanAntichainsKernel.ProductEmbeddingData
import BooleanAntichainsKernel.CoverPairCounting

namespace BooleanAntichainsKernel

open Finset
open scoped Classical

theorem sum_active_cover_by_sizes (k : ℕ) (u v : ℕ → ℕ) :
    (∑ A : Finset (Fin k), ∑ B : Finset (Fin k),
      if A ∪ B = univ then u A.card * v B.card else 0) =
    ∑ a ∈ range (k + 1), ∑ b ∈ range (k + 1),
      k.choose a * a.choose (k - b) * u a * v b := by
  have hA (A : Finset (Fin k)) :
      (∑ B : Finset (Fin k), if A ∪ B = univ then u A.card * v B.card else 0) =
      ∑ b ∈ range (k + 1), A.card.choose (k - b) * u A.card * v b := by
    calc
      _ = u A.card * ∑ B : Finset (Fin k), if A ∪ B = univ then v B.card else 0 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro B _
        split_ifs <;> simp
      _ = u A.card * ∑ b ∈ range (k + 1), A.card.choose (k - b) * v b := by
        rw [sum_covering_partners_by_card]
      _ = _ := by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b _
        ac_rfl
  simp_rw [hA]
  rw [sum_finsets_by_card k (fun a ↦ ∑ b ∈ range (k + 1), a.choose (k - b) * u a * v b)]
  simp only [Finset.mul_sum, Nat.mul_assoc]

variable {L K : Type*}
variable [Fintype L] [DecidableEq L] [Lattice L] [OrderBot L] [OrderTop L]
variable [Fintype K] [DecidableEq K] [Lattice K] [OrderBot K] [OrderTop K]

/-- Count every labelled product embedding using its actual two active sets. -/
theorem productEmbedding_count_by_sizes (k : ℕ) :
    Fintype.card (TopBooleanEmbedding (Fin k) (L × K)) =
      ∑ a ∈ range (k + 1), ∑ b ∈ range (k + 1),
        k.choose a * a.choose (k - b) *
          (a.factorial * Fintype.card (BooleanAntichain a L)) *
          (b.factorial * Fintype.card (BooleanAntichain b K)) := by
  have hL (A : Finset (Fin k)) :
      Fintype.card (TopBooleanEmbedding A L) =
        A.card.factorial * Fintype.card (BooleanAntichain A.card L) := by
    simpa using topBooleanEmbedding_count_general (ι := A) (L := L)
  have hK (B : Finset (Fin k)) :
      Fintype.card (TopBooleanEmbedding B K) =
        B.card.factorial * Fintype.card (BooleanAntichain B.card K) := by
    simpa using topBooleanEmbedding_count_general (ι := B) (L := K)
  rw [productEmbedding_count_cover]
  simp_rw [hL, hK]
  exact sum_active_cover_by_sizes k
    (fun a ↦ a.factorial * Fintype.card (BooleanAntichain a L))
    (fun b ↦ b.factorial * Fintype.card (BooleanAntichain b K))

end BooleanAntichainsKernel
