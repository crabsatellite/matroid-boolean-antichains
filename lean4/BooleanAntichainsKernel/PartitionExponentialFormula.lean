import BooleanAntichainsKernel.OrderedPartitionWeightSum
import BooleanAntichainsKernel.PartitionBellSquareSeries
import BooleanAntichainsKernel.PartitionPairMobiusSum
import Mathlib.Tactic.FieldSimp

namespace BooleanAntichainsKernel

open scoped Classical

noncomputable def partitionBellSquareMobiusSumQ (n : ℕ) : ℚ :=
  ∑ P : Finpartition (Finset.univ : Finset (Fin n)),
    (partitionMobiusCandidate P.parts.card : ℚ) *
      ∏ B : P.parts, (Nat.bell B.1.card : ℚ) ^ 2

theorem partitionBellSquareMobiusSum_cast (n : ℕ) :
    (partitionBellSquareMobiusSum n : ℚ) = partitionBellSquareMobiusSumQ n := by
  unfold partitionBellSquareMobiusSum partitionBellSquareMobiusSumQ
  push_cast
  rfl

theorem partitionBellSquareMobius_inner (n : ℕ)
    (P : Finpartition (Finset.univ : Finset (Fin n))) :
    (∑ b ∈ Finset.range (n + 1),
      if b = P.parts.card then
        (partitionMobiusCandidate b : ℚ) *
          (∏ B : P.parts, (Nat.bell B.1.card : ℚ) ^ 2)
      else 0) =
        (partitionMobiusCandidate P.parts.card : ℚ) *
          ∏ B : P.parts, (Nat.bell B.1.card : ℚ) ^ 2 := by
  have hmem : P.parts.card ∈ Finset.range (n + 1) :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le (by
      simpa only [Finset.card_univ, Fintype.card_fin] using P.card_parts_le_card))
  rw [Finset.sum_ite_eq', if_pos hmem]

theorem partitionBellSquareMobiusSumQ_blocks (n : ℕ) :
    partitionBellSquareMobiusSumQ n =
      ∑ b ∈ Finset.range (n + 1),
        (partitionMobiusCandidate b : ℚ) * partitionBellSquareWeightedCount n b := by
  unfold partitionBellSquareMobiusSumQ partitionBellSquareWeightedCount
  calc
    _ = ∑ P : Finpartition (Finset.univ : Finset (Fin n)),
        ∑ b ∈ Finset.range (n + 1),
          if b = P.parts.card then
            (partitionMobiusCandidate b : ℚ) *
              (∏ B : P.parts, (Nat.bell B.1.card : ℚ) ^ 2)
          else 0 := by
      apply Finset.sum_congr rfl
      intro P _hP
      exact (partitionBellSquareMobius_inner n P).symm
    _ = ∑ b ∈ Finset.range (n + 1),
        ∑ P : Finpartition (Finset.univ : Finset (Fin n)),
          if b = P.parts.card then
            (partitionMobiusCandidate b : ℚ) *
              (∏ B : P.parts, (Nat.bell B.1.card : ℚ) ^ 2)
          else 0 := by rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro b _hb
      let w : Finpartition (Finset.univ : Finset (Fin n)) → ℚ :=
        fun P ↦ ∏ B : P.parts, (Nat.bell B.1.card : ℚ) ^ 2
      have hs :
          (∑ P ∈ Finset.univ.filter
              (fun P : Finpartition (Finset.univ : Finset (Fin n)) ↦ P.parts.card = b), w P) =
            ∑ P : PartitionsWithBlocks (Fin n) b, w P.1 :=
        Finset.sum_subtype
          (p := fun P : Finpartition (Finset.univ : Finset (Fin n)) ↦ P.parts.card = b)
          (Finset.univ.filter
            (fun P : Finpartition (Finset.univ : Finset (Fin n)) ↦ P.parts.card = b))
          (fun P ↦ by simp)
          w
      calc
        (∑ P : Finpartition (Finset.univ : Finset (Fin n)),
            if b = P.parts.card then
              (partitionMobiusCandidate b : ℚ) * w P else 0) =
          (partitionMobiusCandidate b : ℚ) *
            ∑ P ∈ Finset.univ.filter (fun P : Finpartition
              (Finset.univ : Finset (Fin n)) ↦ P.parts.card = b), w P := by
            rw [Finset.mul_sum]
            rw [Finset.sum_filter]
            apply Finset.sum_congr rfl
            intro P _hP
            by_cases h : P.parts.card = b
            · simp [h]
            · have h' : b ≠ P.parts.card := fun h' ↦ h h'.symm
              simp [h, h']
        _ = (partitionMobiusCandidate b : ℚ) *
            ∑ P : PartitionsWithBlocks (Fin n) b, partitionBellSquareWeight P := by
          rw [hs]
          congr 1
        _ = _ := rfl

theorem logFactor_factorial_eq_candidate (b : ℕ) :
    (if b = 0 then 0 else ((-1 : ℚ) ^ (b + 1) / b)) * (b.factorial : ℚ) =
      (partitionMobiusCandidate b : ℚ) := by
  cases b with
  | zero => simp [partitionMobiusCandidate]
  | succ k =>
    rw [if_neg (Nat.succ_ne_zero k), partitionMobiusCandidate_succ,
      Nat.factorial_succ]
    push_cast
    have hk : ((k : ℚ) + 1) ≠ 0 := by positivity
    field_simp
    ring_nf

/-- The manuscript's weighted exponential formula, on the literal
formal logarithm and literal finite set partitions. -/
theorem partition_exponential_formula (n : ℕ) :
    (n.factorial : ℚ) * PowerSeries.coeff n bellSquareLogSeries =
      partitionBellSquareMobiusSumQ n := by
  rw [bellSquareLogSeries_coeff, Finset.mul_sum,
    partitionBellSquareMobiusSumQ_blocks]
  apply Finset.sum_congr rfl
  intro b hb
  calc
    (n.factorial : ℚ) *
        ((if b = 0 then 0 else (-1 : ℚ) ^ (b + 1) / b) *
          PowerSeries.coeff n (bellSquareEGF ^ b)) =
      (if b = 0 then 0 else (-1 : ℚ) ^ (b + 1) / b) *
        ((n.factorial : ℚ) * PowerSeries.coeff n (bellSquareEGF ^ b)) := by ring
    _ = (if b = 0 then 0 else (-1 : ℚ) ^ (b + 1) / b) *
        ((b.factorial : ℚ) * partitionBellSquareWeightedCount n b) := by
      rw [bellSquareEGF_coeff_pow_partition]
    _ = (partitionMobiusCandidate b : ℚ) *
        partitionBellSquareWeightedCount n b := by
      rw [← mul_assoc, logFactor_factorial_eq_candidate]

theorem partition_exponential_formula_integer_cast (n : ℕ) :
    (partitionBellSquareMobiusSum n : ℚ) =
      (n.factorial : ℚ) * PowerSeries.coeff n bellSquareLogSeries := by
  rw [partitionBellSquareMobiusSum_cast, partition_exponential_formula]

end BooleanAntichainsKernel
