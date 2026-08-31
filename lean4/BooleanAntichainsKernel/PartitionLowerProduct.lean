import BooleanAntichainsKernel.PartitionRestriction
import Mathlib.Data.Fintype.BigOperators

namespace BooleanAntichainsKernel

open scoped Classical

variable {α : Type*} [DecidableEq α] {s : Finset α}
variable (P : Finpartition s)

def partitionBindBlocks (R : (B : P.parts) → Finpartition B.1) : Finpartition s :=
  P.bind (fun B hB ↦ R ⟨B, hB⟩)

theorem partitionBindBlocks_mem (R : (B : P.parts) → Finpartition B.1) (C : Finset α) :
    C ∈ (partitionBindBlocks P R).parts ↔ ∃ B : P.parts, C ∈ (R B).parts := by
  constructor
  · intro hC
    obtain ⟨B, hB, hC⟩ := Finpartition.mem_bind.mp hC
    exact ⟨⟨B, hB⟩, hC⟩
  · rintro ⟨B, hC⟩
    exact Finpartition.mem_bind.mpr ⟨B.1, B.2, hC⟩

theorem partitionBindBlocks_le (R : (B : P.parts) → Finpartition B.1) :
    partitionBindBlocks P R ≤ P := by
  intro C hC
  obtain ⟨B, hC⟩ := (partitionBindBlocks_mem P R C).mp hC
  exact ⟨B.1, B.2, (R B).le hC⟩

theorem partitionBindBlocks_mono {R T : (B : P.parts) → Finpartition B.1}
    (h : ∀ B, R B ≤ T B) : partitionBindBlocks P R ≤ partitionBindBlocks P T := by
  intro C hC
  obtain ⟨B, hC⟩ := (partitionBindBlocks_mem P R C).mp hC
  obtain ⟨D, hD, hCD⟩ := h B hC
  exact ⟨D, (partitionBindBlocks_mem P T D).mpr ⟨B, hD⟩, hCD⟩

/-- Restrict the original fine partition to each original coarse block. -/
def partitionLowerToBlocks (Q : Set.Iic P) (B : P.parts) : Finpartition B.1 :=
  Q.1.restrict (P.le B.2)

theorem partitionBindBlocks_lower (Q : Set.Iic P) :
    partitionBindBlocks P (partitionLowerToBlocks P Q) = Q.1 := by
  apply Finpartition.ext
  ext C
  rw [partitionBindBlocks_mem]
  constructor
  · rintro ⟨B, hC⟩
    change C ∈ (Q.1.restrict (P.le B.2)).parts at hC
    rw [partitionRestrict_refinement_parts Q.2 B.2] at hC
    exact (Finset.mem_filter.mp hC).1
  · intro hC
    obtain ⟨B, hB, hCB⟩ := Q.2 hC
    refine ⟨⟨B, hB⟩, ?_⟩
    change C ∈ (Q.1.restrict (P.le hB)).parts
    rw [partitionRestrict_refinement_parts Q.2 hB]
    exact Finset.mem_filter.mpr ⟨hC, hCB⟩

theorem partitionLower_bindBlocks (R : (B : P.parts) → Finpartition B.1) :
    partitionLowerToBlocks P ⟨partitionBindBlocks P R, partitionBindBlocks_le P R⟩ = R := by
  funext B
  apply Finpartition.ext
  change ((partitionBindBlocks P R).restrict (P.le B.2)).parts = (R B).parts
  rw [partitionRestrict_refinement_parts (partitionBindBlocks_le P R) B.2]
  ext C
  rw [Finset.mem_filter, partitionBindBlocks_mem]
  constructor
  · rintro ⟨⟨D, hCD⟩, hCB⟩
    obtain ⟨x, hx⟩ := (R D).nonempty_of_mem_parts hCD
    have hDB : D = B := Subtype.ext (P.eq_of_mem_parts D.2 B.2 ((R D).le hCD hx) (hCB hx))
    exact hDB ▸ hCD
  · intro hC
    exact ⟨⟨B, hC⟩, (R B).le hC⟩

/-- The lower interval is the product of partitions of the actual
original blocks, with the refinement order preserved in both directions. -/
def partitionLowerIntervalOrderIso :
    Set.Iic P ≃o ((B : P.parts) → Finpartition B.1) where
  toFun := partitionLowerToBlocks P
  invFun R := ⟨partitionBindBlocks P R, partitionBindBlocks_le P R⟩
  left_inv Q := Subtype.ext (partitionBindBlocks_lower P Q)
  right_inv := partitionLower_bindBlocks P
  map_rel_iff' := by
    intro Q R
    change partitionLowerToBlocks P Q ≤ partitionLowerToBlocks P R ↔ Q.1 ≤ R.1
    constructor
    · intro h
      have hb := partitionBindBlocks_mono P h
      rw [partitionBindBlocks_lower, partitionBindBlocks_lower] at hb
      exact hb
    · intro h B
      exact partitionRestrict_mono (show Q.1 ≤ R.1 from h) (P.le B.2)

theorem partitionLowerIntervalOrderIso_blocks (Q : Set.Iic P) (B : P.parts) :
    ((partitionLowerIntervalOrderIso P Q) B).parts = Q.1.parts.filter (fun C ↦ C ⊆ B.1) :=
  partitionRestrict_refinement_parts Q.2 B.2

theorem partitionLowerInterval_count :
    Fintype.card (Set.Iic P) = ∏ B : P.parts, Fintype.card (Finpartition B.1) := by
  rw [Fintype.card_congr (partitionLowerIntervalOrderIso P).toEquiv, Fintype.card_pi]

end BooleanAntichainsKernel
