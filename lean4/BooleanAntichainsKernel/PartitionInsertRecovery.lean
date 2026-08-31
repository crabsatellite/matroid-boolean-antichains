import BooleanAntichainsKernel.PartitionInsertPoint

namespace BooleanAntichainsKernel

open scoped Classical

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Delete only the new vertex, keeping the equivalence relation on every
old original vertex. Empty residual blocks are automatically absent. -/
noncomputable def partitionDropPoint (Q : Finpartition (Finset.univ : Finset (Option α))) :
    Finpartition (Finset.univ : Finset α) :=
  Finpartition.ofSetoid ((finitePartitionSetoid Q).comap Option.some)

theorem partitionDropPoint_rel (Q : Finpartition (Finset.univ : Finset (Option α))) (x y : α) :
    finitePartitionSetoid (partitionDropPoint Q) x y ↔ finitePartitionSetoid Q (some x) (some y) := by
  change finitePartitionSetoid (Finpartition.ofSetoid ((finitePartitionSetoid Q).comap Option.some)) x y ↔ _
  rw [finitePartitionSetoid_ofSetoid]
  rfl

theorem partitionDropPoint_insert (P : Finpartition (Finset.univ : Finset α)) (t : Option P.parts) :
    partitionDropPoint (partitionInsertPoint P t) = P := by
  apply finitePartitionSetoidOrderIso.injective
  apply Setoid.ext
  intro x y
  exact (partitionDropPoint_rel (partitionInsertPoint P t) x y).trans (partitionInsertPoint_old_rel P t x y)

/-- Recover the actual old block joined by the new point, or record that
the new point is a singleton. The block is independent of the witness. -/
noncomputable def partitionInsertTarget (Q : Finpartition (Finset.univ : Finset (Option α))) :
    Option (partitionDropPoint Q).parts :=
  if h : ∃ x : α, finitePartitionSetoid Q none (some x) then
    some (finitePartitionBlockOf (partitionDropPoint Q) h.choose)
  else none

theorem partitionInsertTarget_spec (Q : Finpartition (Finset.univ : Finset (Option α))) (x : α) :
    partitionInsertTarget Q = some (finitePartitionBlockOf (partitionDropPoint Q) x) ↔
      finitePartitionSetoid Q none (some x) := by
  by_cases h : ∃ a : α, finitePartitionSetoid Q none (some a)
  · rw [partitionInsertTarget, dif_pos h]
    constructor
    · intro hx
      have hr := (finitePartitionBlockOf_eq_iff (partitionDropPoint Q) h.choose x).mp (Option.some.inj hx)
      exact (finitePartitionSetoid Q).trans' h.choose_spec ((partitionDropPoint_rel Q h.choose x).mp hr)
    · intro hx
      apply congrArg Option.some
      apply (finitePartitionBlockOf_eq_iff (partitionDropPoint Q) h.choose x).mpr
      apply (partitionDropPoint_rel Q h.choose x).mpr
      exact (finitePartitionSetoid Q).trans' ((finitePartitionSetoid Q).symm' h.choose_spec) hx
  · rw [partitionInsertTarget, dif_neg h]
    constructor
    · intro hx
      cases hx
    · intro hx
      exact (h ⟨x, hx⟩).elim

/-- Re-inserting the new vertex with its recovered old block restores
the entire original unordered finite partition. -/
theorem partitionInsertPoint_drop_target (Q : Finpartition (Finset.univ : Finset (Option α))) :
    partitionInsertPoint (partitionDropPoint Q) (partitionInsertTarget Q) = Q := by
  apply finitePartitionSetoidOrderIso.injective
  apply Setoid.ext
  intro x y
  cases x with
  | none =>
    cases y with
    | none =>
      exact iff_of_true
        ((finitePartitionSetoid (partitionInsertPoint (partitionDropPoint Q) (partitionInsertTarget Q))).refl' none)
        ((finitePartitionSetoid Q).refl' none)
    | some y =>
      exact (partitionInsertPoint_none_some (partitionDropPoint Q) (partitionInsertTarget Q) y).trans
        (partitionInsertTarget_spec Q y)
  | some x =>
    cases y with
    | none =>
      have h := (partitionInsertPoint_none_some (partitionDropPoint Q) (partitionInsertTarget Q) x).trans
        (partitionInsertTarget_spec Q x)
      exact ((finitePartitionSetoid (partitionInsertPoint (partitionDropPoint Q) (partitionInsertTarget Q))).comm'
        (x := some x) (y := none)).trans
        (h.trans ((finitePartitionSetoid Q).comm' (x := none) (y := some x)))
    | some y =>
      exact (partitionInsertPoint_old_rel (partitionDropPoint Q) (partitionInsertTarget Q) x y).trans
        (partitionDropPoint_rel Q x y)

end BooleanAntichainsKernel
