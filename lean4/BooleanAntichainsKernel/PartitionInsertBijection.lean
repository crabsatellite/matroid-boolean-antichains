import BooleanAntichainsKernel.PartitionInsertRecovery

namespace BooleanAntichainsKernel

open scoped Classical

theorem partitionOption_eq_of_some_tests {γ : Type*} (t u : Option γ)
    (h : ∀ x : γ, t = some x ↔ u = some x) : t = u := by
  cases t with
  | none =>
    cases u with
    | none => rfl
    | some x =>
      have hbad : (none : Option γ) = some x := (h x).mpr rfl
      cases hbad
  | some x => exact ((h x).mp rfl).symm

variable {α : Type*} [Fintype α] [DecidableEq α]

noncomputable def partitionInsertSigma
    (t : Σ P : Finpartition (Finset.univ : Finset α), Option P.parts) :
    Finpartition (Finset.univ : Finset (Option α)) :=
  partitionInsertPoint t.1 t.2

theorem partitionInsertSigma_injective : Function.Injective (partitionInsertSigma (α := α)) := by
  rintro ⟨P, t⟩ ⟨Q, u⟩ h
  have hPQ : P = Q := (partitionDropPoint_insert P t).symm.trans
    ((congrArg partitionDropPoint h).trans (partitionDropPoint_insert Q u))
  subst Q
  apply congrArg (Sigma.mk P)
  apply partitionOption_eq_of_some_tests
  intro B
  obtain ⟨x, rfl⟩ := finitePartitionBlockOf_surjective P B
  have hs := congrArg finitePartitionSetoid h
  have hr := (Setoid.ext_iff.mp hs) none (some x)
  exact (partitionInsertPoint_none_some P t x).symm.trans
    (hr.trans (partitionInsertPoint_none_some P u x))

theorem partitionInsertSigma_surjective : Function.Surjective (partitionInsertSigma (α := α)) := by
  intro Q
  exact ⟨⟨partitionDropPoint Q, partitionInsertTarget Q⟩, partitionInsertPoint_drop_target Q⟩

/-- A partition after inserting one vertex is uniquely an old partition
and either a new singleton block or one marked existing block. -/
noncomputable def partitionInsertEquiv :
    (Σ P : Finpartition (Finset.univ : Finset α), Option P.parts) ≃
      Finpartition (Finset.univ : Finset (Option α)) :=
  Equiv.ofBijective partitionInsertSigma ⟨partitionInsertSigma_injective, partitionInsertSigma_surjective⟩

theorem partitionInsertEquiv_apply (P : Finpartition (Finset.univ : Finset α)) (t : Option P.parts) :
    partitionInsertEquiv ⟨P, t⟩ = partitionInsertPoint P t := rfl

theorem partitionInsertEquiv_symm (Q : Finpartition (Finset.univ : Finset (Option α))) :
    partitionInsertEquiv.symm Q = ⟨partitionDropPoint Q, partitionInsertTarget Q⟩ := by
  apply partitionInsertEquiv.injective
  rw [Equiv.apply_symm_apply]
  exact (partitionInsertPoint_drop_target Q).symm

theorem partitionInsert_none_class_surjective (P : Finpartition (Finset.univ : Finset α)) :
    Function.Surjective (Option.map (finitePartitionBlockOf P)) := by
  intro t
  cases t with
  | none => exact ⟨none, rfl⟩
  | some B =>
    obtain ⟨x, hx⟩ := finitePartitionBlockOf_surjective P B
    exact ⟨some x, congrArg Option.some hx⟩

theorem partitionInsert_some_class_surjective (P : Finpartition (Finset.univ : Finset α)) (B : P.parts) :
    Function.Surjective (fun x : Option α ↦ x.elim B (finitePartitionBlockOf P)) := by
  intro C
  obtain ⟨x, hx⟩ := finitePartitionBlockOf_surjective P C
  exact ⟨some x, hx⟩

/-- The new-singleton branch increases the number of actual blocks by one. -/
theorem partitionInsertPoint_card_none (P : Finpartition (Finset.univ : Finset α)) :
    (partitionInsertPoint P none).parts.card = P.parts.card + 1 := by
  rw [← finitePartition_block_count (partitionInsertPoint P none), partitionInsertPoint_setoid]
  change Nat.card (Quotient (Setoid.ker (Option.map (finitePartitionBlockOf P)))) = _
  calc
    _ = Nat.card (Option P.parts) :=
      Nat.card_congr (Setoid.quotientKerEquivOfSurjective _ (partitionInsert_none_class_surjective P))
    _ = _ := by simp only [Nat.card_eq_fintype_card, Fintype.card_option, Fintype.card_coe]

/-- Marking an existing block does not change the number of blocks. -/
theorem partitionInsertPoint_card_some (P : Finpartition (Finset.univ : Finset α)) (B : P.parts) :
    (partitionInsertPoint P (some B)).parts.card = P.parts.card := by
  rw [← finitePartition_block_count (partitionInsertPoint P (some B)), partitionInsertPoint_setoid]
  change Nat.card (Quotient (Setoid.ker (fun x : Option α ↦ x.elim B (finitePartitionBlockOf P)))) = _
  calc
    _ = Nat.card P.parts :=
      Nat.card_congr (Setoid.quotientKerEquivOfSurjective _ (partitionInsert_some_class_surjective P B))
    _ = _ := by simp only [Nat.card_eq_fintype_card, Fintype.card_coe]

end BooleanAntichainsKernel
