import BooleanAntichainsKernel.PartitionCoarsening

namespace BooleanAntichainsKernel

open scoped Classical

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Old vertices keep their original block labels. The new vertex either
has a new label or receives one specified existing block label. -/
def partitionInsertSetoid (P : Finpartition (Finset.univ : Finset α)) (t : Option P.parts) :
    Setoid (Option α) :=
  match t with
  | none => Setoid.ker (Option.map (finitePartitionBlockOf P))
  | some B => Setoid.ker (fun x : Option α ↦ x.elim B (finitePartitionBlockOf P))

noncomputable def partitionInsertPoint (P : Finpartition (Finset.univ : Finset α)) (t : Option P.parts) :
    Finpartition (Finset.univ : Finset (Option α)) :=
  Finpartition.ofSetoid (partitionInsertSetoid P t)

theorem partitionInsertPoint_setoid (P : Finpartition (Finset.univ : Finset α)) (t : Option P.parts) :
    finitePartitionSetoid (partitionInsertPoint P t) = partitionInsertSetoid P t :=
  finitePartitionSetoid_ofSetoid _

theorem partitionInsertPoint_old_rel (P : Finpartition (Finset.univ : Finset α))
    (t : Option P.parts) (x y : α) :
    finitePartitionSetoid (partitionInsertPoint P t) (some x) (some y) ↔ finitePartitionSetoid P x y := by
  rw [partitionInsertPoint_setoid]
  cases t with
  | none =>
    change some (finitePartitionBlockOf P x) = some (finitePartitionBlockOf P y) ↔ _
    constructor
    · intro h
      exact (finitePartitionBlockOf_eq_iff P x y).mp (Option.some.inj h)
    · intro h
      exact congrArg Option.some ((finitePartitionBlockOf_eq_iff P x y).mpr h)
  | some B =>
    change finitePartitionBlockOf P x = finitePartitionBlockOf P y ↔ _
    exact finitePartitionBlockOf_eq_iff P x y

theorem partitionInsertPoint_none_some (P : Finpartition (Finset.univ : Finset α))
    (t : Option P.parts) (x : α) :
    finitePartitionSetoid (partitionInsertPoint P t) none (some x) ↔ t = some (finitePartitionBlockOf P x) := by
  rw [partitionInsertPoint_setoid]
  cases t with
  | none => rfl
  | some B =>
    change B = finitePartitionBlockOf P x ↔ some B = some (finitePartitionBlockOf P x)
    exact ⟨congrArg Option.some, Option.some.inj⟩

theorem partitionInsertPoint_new_block_member (P : Finpartition (Finset.univ : Finset α))
    (t : Option P.parts) (x : α) :
    some x ∈ (partitionInsertPoint P t).part none ↔ t = some (finitePartitionBlockOf P x) :=
  (finitePartitionSetoid_rel _ (some x) none).symm.trans
    ((finitePartitionSetoid (partitionInsertPoint P t)).comm'.trans (partitionInsertPoint_none_some P t x))

def partitionSomeEmbedding : α ↪ Option α := ⟨Option.some, fun _ _ h ↦ Option.some.inj h⟩

/-- The new-block case inserts exactly the singleton new vertex. -/
theorem partitionInsertPoint_none_block (P : Finpartition (Finset.univ : Finset α)) :
    (partitionInsertPoint P none).part none = {none} := by
  ext x
  cases x with
  | none =>
    exact iff_of_true ((partitionInsertPoint P none).mem_part (Finset.mem_univ none))
      (Finset.mem_singleton_self none)
  | some x =>
    rw [partitionInsertPoint_new_block_member]
    simp

/-- The existing-block case adds the new vertex to exactly that original
block, with the old vertices embedded by some. -/
theorem partitionInsertPoint_some_block (P : Finpartition (Finset.univ : Finset α)) (B : P.parts) :
    (partitionInsertPoint P (some B)).part none = insert none (B.1.map partitionSomeEmbedding) := by
  ext x
  cases x with
  | none =>
    exact iff_of_true ((partitionInsertPoint P (some B)).mem_part (Finset.mem_univ none))
      (Finset.mem_insert_self _ _)
  | some x =>
    rw [partitionInsertPoint_new_block_member, Option.some.injEq]
    simp only [Finset.mem_insert, Option.some_ne_none, false_or, Finset.mem_map,
      partitionSomeEmbedding, Function.Embedding.coeFn_mk, Option.some.injEq, exists_eq_right]
    exact (Subtype.ext_iff.trans eq_comm).trans (P.part_eq_iff_mem B.2)

end BooleanAntichainsKernel
