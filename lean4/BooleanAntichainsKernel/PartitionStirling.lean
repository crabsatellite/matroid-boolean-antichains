import BooleanAntichainsKernel.FinitePartitionRelabel
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Combinatorics.Enumerative.Stirling

namespace BooleanAntichainsKernel

open scoped Classical

section Boundaries

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem finitePartition_parts_empty [IsEmpty α] (P : Finpartition (Finset.univ : Finset α)) :
    P.parts = ∅ := by
  apply P.parts_eq_empty_iff.mpr
  ext x
  exact isEmptyElim x

theorem partitionsWithBlocks_empty_zero [IsEmpty α] :
    Fintype.card (PartitionsWithBlocks α 0) = 1 := by
  letI : Subsingleton (Finpartition (Finset.univ : Finset α)) :=
    ⟨fun P Q ↦ Finpartition.ext ((finitePartition_parts_empty P).trans (finitePartition_parts_empty Q).symm)⟩
  letI : Nonempty (PartitionsWithBlocks α 0) :=
    ⟨⟨⊥, by rw [finitePartition_parts_empty, Finset.card_empty]⟩⟩
  rw [← Nat.card_eq_fintype_card]
  exact Nat.card_unique

theorem partitionsWithBlocks_empty_succ [IsEmpty α] (k : ℕ) :
    Fintype.card (PartitionsWithBlocks α (k + 1)) = 0 := by
  letI : IsEmpty (PartitionsWithBlocks α (k + 1)) := ⟨fun P ↦ by
    have hz : P.1.parts.card = 0 := by rw [finitePartition_parts_empty, Finset.card_empty]
    exact Nat.succ_ne_zero k (P.2.symm.trans hz)⟩
  exact Fintype.card_eq_zero

theorem partitionsWithBlocks_zero_nonempty [Nonempty α] :
    Fintype.card (PartitionsWithBlocks α 0) = 0 := by
  letI : IsEmpty (PartitionsWithBlocks α 0) := ⟨fun P ↦ by
    obtain ⟨x⟩ := (inferInstance : Nonempty α)
    have hm := P.1.part_mem.mpr (Finset.mem_univ x)
    rw [Finset.card_eq_zero.mp P.2] at hm
    exact Finset.notMem_empty _ hm⟩
  exact Fintype.card_eq_zero

end Boundaries

/-- Defined as the actual finite-block partition cardinality, not as a
recursive number sequence or a supplied Stirling value. -/
noncomputable def finitePartitionCount (n k : ℕ) : ℕ :=
  Fintype.card (PartitionsWithBlocks (Fin n) k)

theorem finitePartitionCount_zero_zero : finitePartitionCount 0 0 = 1 :=
  partitionsWithBlocks_empty_zero (α := Fin 0)

theorem finitePartitionCount_zero_succ (k : ℕ) : finitePartitionCount 0 (k + 1) = 0 :=
  partitionsWithBlocks_empty_succ (α := Fin 0) k

theorem finitePartitionCount_succ_zero (n : ℕ) : finitePartitionCount (n + 1) 0 = 0 := by
  letI : Nonempty (Fin (n + 1)) := ⟨⟨0, Nat.zero_lt_succ n⟩⟩
  exact partitionsWithBlocks_zero_nonempty (α := Fin (n + 1))

/-- The explicit vertex bijection sends 0 to the new point and every
successor to its original old vertex. Its block-preserving transport is
consumed before using the insertion recurrence. -/
theorem finitePartitionCount_succ_succ (n k : ℕ) :
    finitePartitionCount (n + 1) (k + 1) =
      (k + 1) * finitePartitionCount n (k + 1) + finitePartitionCount n k := by
  calc
    _ = Fintype.card (PartitionsWithBlocks (Option (Fin n)) (k + 1)) :=
      partitionsWithBlocks_relabel_count (finSuccEquiv n) (k + 1)
    _ = Fintype.card (PartitionsWithBlocks (Fin n) k) +
        (k + 1) * Fintype.card (PartitionsWithBlocks (Fin n) (k + 1)) :=
      partition_blocks_option_succ (α := Fin n) k
    _ = _ := Nat.add_comm _ _

/-- The combinatorial interpretation of the standard recursively defined
Stirling numbers, proved from the actual partition insertion bijection. -/
theorem finitePartitionCount_eq_stirling (n k : ℕ) :
    finitePartitionCount n k = Nat.stirlingSecond n k := by
  induction n generalizing k with
  | zero =>
    cases k with
    | zero => rw [finitePartitionCount_zero_zero, Nat.stirlingSecond_zero]
    | succ k => rw [finitePartitionCount_zero_succ, Nat.stirlingSecond_zero_succ]
  | succ n ih =>
    cases k with
    | zero => rw [finitePartitionCount_succ_zero, Nat.stirlingSecond_succ_zero]
    | succ k =>
      rw [finitePartitionCount_succ_succ, Nat.stirlingSecond_succ_succ, ih (k + 1), ih k]

theorem partitionsWithBlocks_card {α : Type*} [Fintype α] [DecidableEq α] (k : ℕ) :
    Fintype.card (PartitionsWithBlocks α k) = Nat.stirlingSecond (Fintype.card α) k :=
  (partitionsWithBlocks_relabel_count (Fintype.equivFin α) k).trans
    (finitePartitionCount_eq_stirling (Fintype.card α) k)

end BooleanAntichainsKernel
