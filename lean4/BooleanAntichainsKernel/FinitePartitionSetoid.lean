import Mathlib.Data.Setoid.Basic
import Mathlib.Data.Setoid.Partition

namespace BooleanAntichainsKernel

open scoped Classical

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The same-block relation of the actual finite family of nonempty,
pairwise disjoint blocks covering the entire original type. -/
def finitePartitionSetoid (P : Finpartition (Finset.univ : Finset α)) : Setoid α :=
  Setoid.ker P.part

theorem finitePartitionSetoid_rel (P : Finpartition (Finset.univ : Finset α)) (x y : α) :
    finitePartitionSetoid P x y ↔ x ∈ P.part y := by
  change P.part x = P.part y ↔ x ∈ P.part y
  exact (P.mem_part_iff_part_eq_part (Finset.mem_univ x) (Finset.mem_univ y)).symm

theorem finitePartitionSetoid_same_block (P : Finpartition (Finset.univ : Finset α)) (x y : α) :
    finitePartitionSetoid P x y ↔ ∃ B ∈ P.parts, x ∈ B ∧ y ∈ B :=
  (finitePartitionSetoid_rel P x y).trans P.mem_part_iff_exists

theorem finitePartition_part_coe (P : Finpartition (Finset.univ : Finset α)) (x : α) :
    (P.part x : Set α) = {y | finitePartitionSetoid P y x} := by
  ext y
  exact (finitePartitionSetoid_rel P y x).symm

theorem finitePartitionSetoid_classes (P : Finpartition (Finset.univ : Finset α)) :
    (finitePartitionSetoid P).classes =
      (fun B : Finset α ↦ (B : Set α)) '' (P.parts : Set (Finset α)) := by
  ext C
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨P.part x, P.part_mem.mpr (Finset.mem_univ x), finitePartition_part_coe P x⟩
  · rintro ⟨B, hB, rfl⟩
    obtain ⟨x, hx⟩ := P.nonempty_of_mem_parts hB
    refine ⟨x, ?_⟩
    rw [← P.part_eq_of_mem hB hx]
    exact finitePartition_part_coe P x

theorem finitePartition_ext_part {P Q : Finpartition (Finset.univ : Finset α)}
    (h : ∀ x : α, P.part x = Q.part x) : P = Q := by
  apply Finpartition.ext
  ext B
  constructor
  · intro hB
    obtain ⟨x, hx⟩ := P.nonempty_of_mem_parts hB
    have hQ : Q.part x = B := (h x).symm.trans (P.part_eq_of_mem hB hx)
    rw [← hQ]
    exact Q.part_mem.mpr (Finset.mem_univ x)
  · intro hB
    obtain ⟨x, hx⟩ := Q.nonempty_of_mem_parts hB
    have hP : P.part x = B := (h x).trans (Q.part_eq_of_mem hB hx)
    rw [← hP]
    exact P.part_mem.mpr (Finset.mem_univ x)

theorem finitePartitionSetoid_ofSetoid (s : Setoid α) :
    finitePartitionSetoid (Finpartition.ofSetoid s) = s := by
  apply Setoid.ext
  intro x y
  change (Finpartition.ofSetoid s).part x = (Finpartition.ofSetoid s).part y ↔ s x y
  constructor
  · intro h
    have hy : y ∈ (Finpartition.ofSetoid s).part y :=
      (Finpartition.ofSetoid s).mem_part (Finset.mem_univ y)
    rw [← h] at hy
    exact Finpartition.mem_part_ofSetoid_iff_rel.mp hy
  · intro h
    have hy : y ∈ (Finpartition.ofSetoid s).part x := Finpartition.mem_part_ofSetoid_iff_rel.mpr h
    exact ((Finpartition.ofSetoid s).part_eq_of_mem
      ((Finpartition.ofSetoid s).part_mem.mpr (Finset.mem_univ x)) hy).symm

theorem finitePartition_ofSetoid_setoid (P : Finpartition (Finset.univ : Finset α)) :
    Finpartition.ofSetoid (finitePartitionSetoid P) = P := by
  apply finitePartition_ext_part
  intro x
  ext y
  rw [Finpartition.mem_part_ofSetoid_iff_rel]
  change P.part x = P.part y ↔ y ∈ P.part x
  exact eq_comm.trans (P.mem_part_iff_part_eq_part (Finset.mem_univ y) (Finset.mem_univ x)).symm

/-- Refinement is exactly inclusion of the same-block relations. -/
theorem finitePartitionSetoid_le_iff (P Q : Finpartition (Finset.univ : Finset α)) :
    finitePartitionSetoid P ≤ finitePartitionSetoid Q ↔ P ≤ Q := by
  constructor
  · intro h B hB
    obtain ⟨x, hx⟩ := P.nonempty_of_mem_parts hB
    refine ⟨Q.part x, Q.part_mem.mpr (Finset.mem_univ x), ?_⟩
    intro y hy
    apply (finitePartitionSetoid_rel Q y x).mp
    apply h
    apply (finitePartitionSetoid_rel P y x).mpr
    rw [P.part_eq_of_mem hB hx]
    exact hy
  · intro h x y hxy
    have hPx := P.part_mem.mpr (Finset.mem_univ x)
    obtain ⟨B, hB, hsub⟩ := h hPx
    have hxB : x ∈ B := hsub (P.mem_part (Finset.mem_univ x))
    have hyP : y ∈ P.part x := (finitePartitionSetoid_rel P y x).mp
      ((finitePartitionSetoid P).symm' hxy)
    change Q.part x = Q.part y
    exact (Q.part_eq_of_mem hB hxB).trans (Q.part_eq_of_mem hB (hsub hyP)).symm

noncomputable def finitePartitionSetoidOrderIso :
    Finpartition (Finset.univ : Finset α) ≃o Setoid α where
  toFun := finitePartitionSetoid
  invFun s := Finpartition.ofSetoid s
  left_inv := finitePartition_ofSetoid_setoid
  right_inv := finitePartitionSetoid_ofSetoid
  map_rel_iff' := finitePartitionSetoid_le_iff _ _

end BooleanAntichainsKernel
