import BooleanAntichainsKernel.FinitePartitionLattice

namespace BooleanAntichainsKernel

open scoped Classical

variable {α : Type*} [DecidableEq α] {s B : Finset α}

theorem partitionRestrict_mem (Q : Finpartition s) (hB : B ⊆ s) (C : Finset α) :
    C ∈ (Q.restrict hB).parts ↔ C ≠ ∅ ∧ ∃ D ∈ Q.parts, D ∩ B = C := by
  change C ∈ (Q.parts.image (fun D ↦ D ∩ B)).erase ∅ ↔ _
  rw [Finset.mem_erase, Finset.mem_image]

/-- Restriction preserves the actual refinement order. -/
theorem partitionRestrict_mono {Q R : Finpartition s} (hQR : Q ≤ R) (hB : B ⊆ s) :
    Q.restrict hB ≤ R.restrict hB := by
  intro C hC
  obtain ⟨hne, D, hD, rfl⟩ := (partitionRestrict_mem Q hB C).mp hC
  obtain ⟨E, hE, hDE⟩ := hQR hD
  have hsub : D ∩ B ⊆ E ∩ B := by
    intro x hx
    exact Finset.mem_inter.mpr ⟨hDE (Finset.mem_inter.mp hx).1, (Finset.mem_inter.mp hx).2⟩
  have hne' : E ∩ B ≠ ∅ := Finset.nonempty_iff_ne_empty.mp
    ((Finset.nonempty_iff_ne_empty.mpr hne).mono hsub)
  exact ⟨E ∩ B, (partitionRestrict_mem R hB _).mpr ⟨hne', E, hE, rfl⟩, hsub⟩

/-- When Q refines P, restricting Q to a block of P keeps precisely the
whole Q-blocks contained there; no new intersection pieces are introduced. -/
theorem partitionRestrict_refinement_parts {P Q : Finpartition s} (hQP : Q ≤ P)
    (hB : B ∈ P.parts) :
    (Q.restrict (P.le hB)).parts = Q.parts.filter (fun C ↦ C ⊆ B) := by
  ext C
  constructor
  · intro hC
    obtain ⟨hne, D, hD, hDC⟩ := (partitionRestrict_mem Q (P.le hB) C).mp hC
    obtain ⟨E, hE, hDE⟩ := hQP hD
    obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    have hxDB : x ∈ D ∩ B := by rw [hDC]; exact hx
    have hEB : E = B := P.eq_of_mem_parts hE hB
      (hDE (Finset.mem_inter.mp hxDB).1) (Finset.mem_inter.mp hxDB).2
    subst E
    have hEq : D = C := by simpa only [Finset.inter_eq_left.mpr hDE] using hDC
    rw [← hEq]
    exact Finset.mem_filter.mpr ⟨hD, hDE⟩
  · intro hC
    obtain ⟨hC, hCB⟩ := Finset.mem_filter.mp hC
    exact (partitionRestrict_mem Q (P.le hB) C).mpr
      ⟨Q.ne_empty hC, C, hC, Finset.inter_eq_left.mpr hCB⟩

end BooleanAntichainsKernel
