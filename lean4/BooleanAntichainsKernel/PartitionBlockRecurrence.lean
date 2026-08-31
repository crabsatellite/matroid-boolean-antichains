import BooleanAntichainsKernel.PartitionInsertBijection
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace BooleanAntichainsKernel

open scoped Classical

theorem partition_card_subtype_indicator {γ : Type*} [Fintype γ] (p : γ → Prop)
    [Fintype {x : γ // p x}] [DecidablePred p] :
    Fintype.card {x : γ // p x} = ∑ x : γ, if p x then (1 : ℕ) else 0 := by
  rw [Fintype.card_subtype, Finset.card_eq_sum_ones, Finset.sum_filter]

abbrev PartitionsWithBlocks (α : Type*) [Fintype α] [DecidableEq α] (k : ℕ) :=
  {P : Finpartition (Finset.univ : Finset α) // P.parts.card = k}

variable {α : Type*} [Fintype α] [DecidableEq α]

noncomputable instance {k : ℕ} : Fintype (PartitionsWithBlocks α k) := Subtype.fintype _

/-- The size stratum is split over the actual old partition and the
eligible insertion choices; both maps merely regroup the same data. -/
noncomputable def partitionInsertStratumEquiv (b : ℕ) :
    PartitionsWithBlocks (Option α) b ≃
      Σ P : Finpartition (Finset.univ : Finset α),
        {t : Option P.parts // (partitionInsertPoint P t).parts.card = b} := by
  let e :
      {t : Σ P : Finpartition (Finset.univ : Finset α), Option P.parts //
        (partitionInsertPoint t.1 t.2).parts.card = b} ≃ PartitionsWithBlocks (Option α) b :=
    (partitionInsertEquiv (α := α)).subtypeEquiv (fun _ ↦ Iff.rfl)
  exact e.symm.trans
    { toFun := fun t ↦ ⟨t.1.1, ⟨t.1.2, t.2⟩⟩
      invFun := fun t ↦ ⟨⟨t.1, t.2.1⟩, t.2.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }

theorem partitionInsert_fibre_card (P : Finpartition (Finset.univ : Finset α)) (k : ℕ) :
    Fintype.card {t : Option P.parts // (partitionInsertPoint P t).parts.card = k + 1} =
      (if P.parts.card = k then 1 else 0) +
        (if P.parts.card = k + 1 then P.parts.card else 0) := by
  rw [partition_card_subtype_indicator, Fintype.sum_option, partitionInsertPoint_card_none]
  simp_rw [partitionInsertPoint_card_some]
  by_cases h : P.parts.card = k + 1 <;> simp [h]

/-- The Stirling recurrence is derived on literal unordered finite-block
partitions. The factor k+1 is earned from the actual existing-block fibre. -/
theorem partition_blocks_option_succ (k : ℕ) :
    Fintype.card (PartitionsWithBlocks (Option α) (k + 1)) =
      Fintype.card (PartitionsWithBlocks α k) +
        (k + 1) * Fintype.card (PartitionsWithBlocks α (k + 1)) := by
  rw [Fintype.card_congr (partitionInsertStratumEquiv (α := α) (k + 1)), Fintype.card_sigma]
  simp_rw [partitionInsert_fibre_card]
  rw [Finset.sum_add_distrib]
  have hw (P : Finpartition (Finset.univ : Finset α)) :
      (if P.parts.card = k + 1 then P.parts.card else 0) =
        (k + 1) * (if P.parts.card = k + 1 then 1 else 0) := by
    by_cases h : P.parts.card = k + 1 <;> simp [h]
  simp_rw [hw]
  rw [← Finset.mul_sum]
  rw [← partition_card_subtype_indicator (fun P : Finpartition (Finset.univ : Finset α) ↦ P.parts.card = k),
    ← partition_card_subtype_indicator (fun P : Finpartition (Finset.univ : Finset α) ↦ P.parts.card = k + 1)]

end BooleanAntichainsKernel
