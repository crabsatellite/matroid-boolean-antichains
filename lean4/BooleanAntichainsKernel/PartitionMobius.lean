import BooleanAntichainsKernel.PartitionMobiusWeightedSum
import BooleanAntichainsKernel.PartitionFlatRank
import Mathlib.Combinatorics.Enumerative.IncidenceAlgebra

namespace BooleanAntichainsKernel

open scoped Classical

variable {α : Type*} [Fintype α] [DecidableEq α]

noncomputable local instance partitionLocallyFiniteOrder :
    LocallyFiniteOrder (Finpartition (Finset.univ : Finset α)) :=
  Fintype.toLocallyFiniteOrder

theorem finitePartition_top_parts [Nonempty α] :
    (⊤ : Finpartition (Finset.univ : Finset α)).parts = {Finset.univ} := by
  apply Finset.Subset.antisymm
  · exact Finpartition.parts_top_subset _
  · obtain ⟨B, hB⟩ := (⊤ : Finpartition (Finset.univ : Finset α)).parts_nonempty (by
      intro h
      have hx : (Classical.choice (inferInstance : Nonempty α)) ∈ (Finset.univ : Finset α) := Finset.mem_univ _
      rw [h] at hx
      exact Finset.notMem_empty _ hx)
    have hEq : B = Finset.univ :=
      Finset.mem_singleton.mp (Finpartition.parts_top_subset _ hB)
    exact Finset.singleton_subset_iff.mpr (hEq ▸ hB)

theorem finitePartition_top_card [Nonempty α] :
    (⊤ : Finpartition (Finset.univ : Finset α)).parts.card = 1 := by
  rw [finitePartition_top_parts, Finset.card_singleton]

theorem finitePartition_strict_block_count {P Q : Finpartition (Finset.univ : Finset α)}
    (hPQ : P < Q) : Q.parts.card < P.parts.card := by
  have hr := MatroidFlat.rank_strictMono
    ((finitePartitionCompleteFlatOrderIso (α := α)).lt_iff_lt.mpr hPQ)
  rw [partitionFlat_rank, partitionFlat_rank] at hr
  have hp := P.card_parts_le_card
  have hq := Q.card_parts_le_card
  simp only [Finset.card_univ] at hp hq
  omega

theorem partitionCandidate_sum_Icc [Nonempty α]
    (P : Finpartition (Finset.univ : Finset α)) :
    (∑ Q ∈ Finset.Icc P (⊤ : Finpartition (Finset.univ : Finset α)),
      partitionMobiusCandidate Q.parts.card) =
        if P = ⊤ then 1 else 0 := by
  letI : Fintype (Set.Ici P) := Subtype.fintype _
  calc
    _ = ∑ Q : Set.Ici P, partitionMobiusCandidate Q.1.parts.card := by
      exact Finset.sum_subtype (Finset.Icc P (⊤ : Finpartition (Finset.univ : Finset α)))
        (fun Q ↦ by simp) (fun Q ↦ partitionMobiusCandidate Q.parts.card)
    _ = partitionMobiusConvolution P.parts.card :=
      partitionCoarsening_mobius_weighted_sum P
    _ = _ := by
      by_cases hP : P = ⊤
      · subst P
        rw [if_pos rfl, finitePartition_top_card, partitionMobiusConvolution_one]
      · rw [if_neg hP]
        have hlt : 1 < P.parts.card := by
          rw [← finitePartition_top_card (α := α)]
          exact finitePartition_strict_block_count (lt_of_le_of_ne le_top hP)
        obtain ⟨n, hn⟩ : ∃ n, P.parts.card = n + 1 := ⟨P.parts.card - 1, by omega⟩
        rw [hn, partitionMobiusConvolution_succ n (by omega)]

/-- The exact incidence-algebra Möbius value used by the manuscript,
proved from its defining recurrence and the checked Stirling convolution. -/
theorem finitePartition_mu_top [Nonempty α]
    (P : Finpartition (Finset.univ : Finset α)) :
    IncidenceAlgebra.mu ℤ P (⊤ : Finpartition (Finset.univ : Finset α)) =
      partitionMobiusCandidate P.parts.card := by
  induction hcard : P.parts.card using Nat.strong_induction_on generalizing P with
  | h b ih =>
    by_cases hP : P = ⊤
    · subst P
      rw [IncidenceAlgebra.mu_self, ← hcard, finitePartition_top_card,
        partitionMobiusCandidate_succ]
      norm_num
    · have hpt : P < (⊤ : Finpartition (Finset.univ : Finset α)) :=
        lt_of_le_of_ne le_top hP
      rw [IncidenceAlgebra.mu_eq_neg_sum_Ioc_of_ne hP]
      have hsum :
          (∑ Q ∈ Finset.Ioc P (⊤ : Finpartition (Finset.univ : Finset α)),
            IncidenceAlgebra.mu ℤ Q (⊤ : Finpartition (Finset.univ : Finset α))) =
          ∑ Q ∈ Finset.Ioc P (⊤ : Finpartition (Finset.univ : Finset α)),
            partitionMobiusCandidate Q.parts.card := by
        apply Finset.sum_congr rfl
        intro Q hQ
        have hPQ : P < Q := (Finset.mem_Ioc.mp hQ).1
        exact ih Q.parts.card (by
          rw [← hcard]
          exact finitePartition_strict_block_count hPQ) Q rfl
      rw [hsum]
      have hc := partitionCandidate_sum_Icc P
      rw [if_neg hP, Finset.Icc_eq_cons_Ioc le_top, Finset.sum_cons] at hc
      rw [← hcard]
      omega

theorem finitePartition_mu_top_formula [Nonempty α]
    (P : Finpartition (Finset.univ : Finset α)) :
    IncidenceAlgebra.mu ℤ P (⊤ : Finpartition (Finset.univ : Finset α)) =
      (-1 : ℤ) ^ (P.parts.card - 1) * (P.parts.card - 1).factorial := by
  rw [finitePartition_mu_top, partitionMobiusCandidate]
  have hu : (Finset.univ : Finset α) ≠ ∅ := by
    intro h
    obtain ⟨x⟩ := (inferInstance : Nonempty α)
    have hx : x ∈ (Finset.univ : Finset α) := Finset.mem_univ x
    rw [h] at hx
    exact Finset.notMem_empty _ hx
  exact if_neg (Finset.card_ne_zero.mpr (P.parts_nonempty hu))

end BooleanAntichainsKernel
