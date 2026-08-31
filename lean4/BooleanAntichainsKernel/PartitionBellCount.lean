import BooleanAntichainsKernel.PartitionMarkedBlock
import BooleanAntichainsKernel.PartitionStirling
import Mathlib.Combinatorics.Enumerative.Bell
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Fintype.Powerset

namespace BooleanAntichainsKernel

open scoped Classical

noncomputable def finitePartitionTotalCount (n : ℕ) : ℕ :=
  Fintype.card (Finpartition (Finset.univ : Finset (Fin n)))

theorem finitePartitionTotalCount_zero : finitePartitionTotalCount 0 = 1 := by
  letI : Unique (Finpartition (Finset.univ : Finset (Fin 0))) := {
    default := ⊥
    uniq := fun P ↦ Finpartition.ext
      ((finitePartition_parts_empty P).trans (finitePartition_parts_empty (⊥ : Finpartition Finset.univ)).symm) }
  exact Fintype.card_unique

theorem nonemptyFinsetSubtype_sum {α : Type*} [Fintype α] [DecidableEq α] (f : Finset α → ℕ) :
    f ∅ + ∑ C : {C : Finset α // C.Nonempty}, f C.1 = ∑ C : Finset α, f C := by
  letI : Unique {C : Finset α // ¬C.Nonempty} := {
    default := ⟨∅, by simp⟩
    uniq := fun C ↦ Subtype.ext (Finset.not_nonempty_iff_eq_empty.mp C.2) }
  have hneg : (∑ C : {C : Finset α // ¬C.Nonempty}, f C.1) = f ∅ := by
    rw [Fintype.sum_unique]
    rfl
  rw [add_comm, ← hneg]
  exact Fintype.sum_subtype_add_sum_subtype (fun C : Finset α ↦ C.Nonempty) f

theorem finitePartitionTotalCount_eq_bell (n : ℕ) :
    finitePartitionTotalCount n = Nat.bell n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simpa using finitePartitionTotalCount_zero
    | succ n =>
      calc
        finitePartitionTotalCount (n + 1) =
            Fintype.card (Finpartition (Finset.univ : Finset (Option (Fin n)))) :=
          Fintype.card_congr (finitePartitionRelabelEquiv (finSuccEquiv n))
        _ = finitePartitionTotalCount n +
            ∑ C : {C : Finset (Fin n) // C.Nonempty},
              Fintype.card (Finpartition ((Finset.univ : Finset (Fin n)) \ C.1)) :=
          partition_option_total_split
        _ = Nat.bell n +
            ∑ C : {C : Finset (Fin n) // C.Nonempty}, Nat.bell (n - C.1.card) := by
          rw [ih n (Nat.lt_succ_self n)]
          apply congrArg₂ (· + ·) rfl
          apply Fintype.sum_congr
          intro C
          calc
            Fintype.card (Finpartition ((Finset.univ : Finset (Fin n)) \ C.1)) =
                finitePartitionTotalCount (((Finset.univ : Finset (Fin n)) \ C.1).card) :=
              supportedPartition_count_fin _
            _ = Nat.bell (((Finset.univ : Finset (Fin n)) \ C.1).card) :=
              ih _ (by
                have hc : 0 < C.1.card := Finset.card_pos.mpr C.2
                have hsub : C.1 ⊆ (Finset.univ : Finset (Fin n)) := Finset.subset_univ _
                simp only [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
                omega)
            _ = Nat.bell (n - C.1.card) := by
              simp only [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
        _ = ∑ C : Finset (Fin n), Nat.bell (n - C.card) :=
          nonemptyFinsetSubtype_sum (fun C : Finset (Fin n) ↦ Nat.bell (n - C.card))
        _ = ∑ i ∈ Finset.range (n + 1), n.choose i * Nat.bell (n - i) := by
          rw [← Finset.powerset_univ,
            Finset.sum_powerset_apply_card (fun i ↦ Nat.bell (n - i))]
          simp only [Finset.card_univ, Fintype.card_fin, Nat.nsmul_eq_mul]
        _ = Nat.bell (n + 1) := by
          rw [Nat.bell_succ, ← Nat.range_succ_eq_Iic]

theorem finitePartition_card_bell {α : Type*} [Fintype α] [DecidableEq α] :
    Fintype.card (Finpartition (Finset.univ : Finset α)) = Nat.bell (Fintype.card α) :=
  (Fintype.card_congr (finitePartitionRelabelEquiv (Fintype.equivFin α))).trans
    (finitePartitionTotalCount_eq_bell (Fintype.card α))

end BooleanAntichainsKernel
