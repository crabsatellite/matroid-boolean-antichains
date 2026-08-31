import BooleanAntichainsKernel.PartitionCoarsening
import BooleanAntichainsKernel.PartitionAntichains

namespace BooleanAntichainsKernel

open scoped Classical

variable {α : Type*} [Fintype α] [DecidableEq α]

noncomputable def partitionCoarseningQuotientMap (P : Finpartition (Finset.univ : Finset α)) (Q : Set.Ici P) :
    Quotient (finitePartitionSetoid Q.1) →
      Quotient (finitePartitionSetoid (partitionCoarseningOrderIso P Q)) :=
  Quotient.lift (fun x ↦ Quotient.mk _ (finitePartitionBlockOf P x))
    (fun x y h ↦ Quotient.sound ((partitionCoarseningOrderIso_rel P Q x y).mpr h))

theorem partitionCoarseningQuotientMap_injective (P : Finpartition (Finset.univ : Finset α))
    (Q : Set.Ici P) : Function.Injective (partitionCoarseningQuotientMap P Q) := by
  intro u v h
  induction u using Quotient.inductionOn with
  | h x =>
    induction v using Quotient.inductionOn with
    | h y =>
      apply Quotient.sound
      exact (partitionCoarseningOrderIso_rel P Q x y).mp (Quotient.exact h)

theorem partitionCoarseningQuotientMap_surjective (P : Finpartition (Finset.univ : Finset α))
    (Q : Set.Ici P) : Function.Surjective (partitionCoarseningQuotientMap P Q) := by
  intro q
  induction q using Quotient.inductionOn with
  | h B =>
    obtain ⟨x, rfl⟩ := finitePartitionBlockOf_surjective P B
    exact ⟨Quotient.mk _ x, rfl⟩

noncomputable def partitionCoarseningQuotientEquiv (P : Finpartition (Finset.univ : Finset α))
    (Q : Set.Ici P) :
    Quotient (finitePartitionSetoid Q.1) ≃
      Quotient (finitePartitionSetoid (partitionCoarseningOrderIso P Q)) :=
  Equiv.ofBijective (partitionCoarseningQuotientMap P Q)
    ⟨partitionCoarseningQuotientMap_injective P Q, partitionCoarseningQuotientMap_surjective P Q⟩

/-- Actual coarse blocks biject to groups of original fine blocks. -/
noncomputable def partitionCoarseningBlockEquiv (P : Finpartition (Finset.univ : Finset α))
    (Q : Set.Ici P) : Q.1.parts ≃ (partitionCoarseningOrderIso P Q).parts :=
  (finitePartitionQuotientBlockEquiv Q.1).symm.trans
    ((partitionCoarseningQuotientEquiv P Q).trans
      (finitePartitionQuotientBlockEquiv (partitionCoarseningOrderIso P Q)))

theorem partitionCoarseningBlockEquiv_blockOf (P : Finpartition (Finset.univ : Finset α))
    (Q : Set.Ici P) (x : α) :
    partitionCoarseningBlockEquiv P Q (finitePartitionBlockOf Q.1 x) =
      finitePartitionBlockOf (partitionCoarseningOrderIso P Q) (finitePartitionBlockOf P x) := by
  change finitePartitionQuotientBlockEquiv (partitionCoarseningOrderIso P Q)
    (partitionCoarseningQuotientEquiv P Q ((finitePartitionQuotientBlockEquiv Q.1).symm
      (finitePartitionQuotientBlockEquiv Q.1 (Quotient.mk (finitePartitionSetoid Q.1) x)))) = _
  rw [Equiv.symm_apply_apply]
  rfl

theorem partitionCoarseningBlockEquiv_membership (P : Finpartition (Finset.univ : Finset α))
    (Q : Set.Ici P) (D : Q.1.parts) (x : α) :
    finitePartitionBlockOf P x ∈ (partitionCoarseningBlockEquiv P Q D).1 ↔ x ∈ D.1 := by
  obtain ⟨a, ha⟩ := Q.1.nonempty_of_mem_parts D.2
  have hD : finitePartitionBlockOf Q.1 a = D := Subtype.ext (Q.1.part_eq_of_mem D.2 ha)
  rw [← hD, partitionCoarseningBlockEquiv_blockOf]
  change finitePartitionBlockOf P x ∈ (partitionCoarseningOrderIso P Q).part (finitePartitionBlockOf P a) ↔
    x ∈ Q.1.part a
  rw [← finitePartitionSetoid_rel, partitionCoarseningOrderIso_rel, finitePartitionSetoid_rel]

/-- Expanding each grouped fine block restores the exact original coarse
block, with all original vertices and no omitted or additional elements. -/
theorem partitionCoarseningBlockEquiv_union (P : Finpartition (Finset.univ : Finset α))
    (Q : Set.Ici P) (D : Q.1.parts) :
    (partitionCoarseningBlockEquiv P Q D).1.biUnion (fun B : P.parts ↦ B.1) = D.1 := by
  ext x
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨B, hB, hxB⟩
    have hBx : finitePartitionBlockOf P x = B := Subtype.ext (P.part_eq_of_mem B.2 hxB)
    apply (partitionCoarseningBlockEquiv_membership P Q D x).mp
    rwa [hBx]
  · intro hx
    exact ⟨finitePartitionBlockOf P x, (partitionCoarseningBlockEquiv_membership P Q D x).mpr hx,
      P.mem_part (Finset.mem_univ x)⟩

theorem partitionCoarsening_blocks_card (P : Finpartition (Finset.univ : Finset α)) (Q : Set.Ici P) :
    (partitionCoarseningOrderIso P Q).parts.card = Q.1.parts.card := by
  have h := Fintype.card_congr (partitionCoarseningBlockEquiv P Q)
  simpa only [Fintype.card_coe] using h.symm

/-- Relative rank is earned from refinement and the proved block
bijection, before it is used for matroid contraction ranks. -/
theorem partitionCoarsening_rank_add (P : Finpartition (Finset.univ : Finset α)) (Q : Set.Ici P) :
    partitionRank (partitionCoarseningOrderIso P Q) + partitionRank P = partitionRank Q.1 := by
  unfold partitionRank
  rw [Fintype.card_coe, partitionCoarsening_blocks_card]
  have hqp := Finpartition.card_mono Q.2
  have hpn := P.card_parts_le_card
  rw [Finset.card_univ] at hpn
  omega

end BooleanAntichainsKernel
