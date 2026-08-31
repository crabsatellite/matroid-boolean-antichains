import BooleanAntichainsKernel.SizedDisjointBlocks
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

namespace BooleanAntichainsKernel

open Finset
open scoped Classical

variable {ι α : Type*} {A : Finset α} {p : ι → ℕ}

def blockSlotEmbedding (g : (Σ i, Fin (p i)) ↪ A) (i : ι) : Fin (p i) ↪ α :=
  ((Function.Embedding.sigmaMk i).trans g).trans (Function.Embedding.subtype (fun a ↦ a ∈ A))

def blocksOfSlotEmbedding (g : (Σ i, Fin (p i)) ↪ A) (i : ι) : Finset α :=
  univ.map (blockSlotEmbedding g i)

lemma blocksOfSlotEmbedding_subset (g : (Σ i, Fin (p i)) ↪ A) (i : ι) :
    blocksOfSlotEmbedding g i ⊆ A := by
  intro z hz
  rcases Finset.mem_map.mp hz with ⟨j, _, rfl⟩
  exact (g ⟨i, j⟩).2

lemma blocksOfSlotEmbedding_card (g : (Σ i, Fin (p i)) ↪ A) (i : ι) :
    (blocksOfSlotEmbedding g i).card = p i := by simp [blocksOfSlotEmbedding]

lemma blocksOfSlotEmbedding_pairwise (g : (Σ i, Fin (p i)) ↪ A) :
    Pairwise fun i j ↦ Disjoint (blocksOfSlotEmbedding g i) (blocksOfSlotEmbedding g j) := by
  intro i j hij
  apply Finset.disjoint_left.mpr
  intro z hzi hzj
  rcases Finset.mem_map.mp hzi with ⟨a, _, ha⟩
  rcases Finset.mem_map.mp hzj with ⟨b, _, hb⟩
  have hv : (g ⟨i, a⟩).1 = (g ⟨j, b⟩).1 := ha.trans hb.symm
  exact hij (congrArg Sigma.fst (g.injective (Subtype.ext hv)))

def slotEmbeddingToBlocks (g : (Σ i, Fin (p i)) ↪ A) : SizedDisjointBlocks A p :=
  ⟨blocksOfSlotEmbedding g, blocksOfSlotEmbedding_subset g, blocksOfSlotEmbedding_card g,
    blocksOfSlotEmbedding_pairwise g⟩

noncomputable def blockSlotEquiv (g : (Σ i, Fin (p i)) ↪ A) (i : ι) :
    Fin (p i) ≃ ↥((slotEmbeddingToBlocks g).1 i) :=
  Equiv.ofBijective
    (fun j ↦ ⟨blockSlotEmbedding g i j, Finset.mem_map.mpr ⟨j, Finset.mem_univ j, rfl⟩⟩)
    ⟨fun _ _ h ↦ (blockSlotEmbedding g i).injective
        (congrArg (fun z : ↥((slotEmbeddingToBlocks g).1 i) ↦ z.1) h),
      fun z ↦ by
        rcases Finset.mem_map.mp z.2 with ⟨j, _, hj⟩
        exact ⟨j, Subtype.ext hj⟩⟩

noncomputable def slotEmbeddingToEnumeratedBlocks (g : (Σ i, Fin (p i)) ↪ A) :
    EnumeratedSizedBlocks A p := ⟨slotEmbeddingToBlocks g, blockSlotEquiv g⟩

theorem enumeratedBlocksToEmbedding_slot_inverse (g : (Σ i, Fin (p i)) ↪ A) :
    enumeratedBlocksToEmbedding (slotEmbeddingToEnumeratedBlocks g) = g := by
  apply Function.Embedding.ext
  rintro ⟨i, j⟩
  apply Subtype.ext
  rfl

/-- Full bijection between numbered actual disjoint blocks and injections
of their disjoint labelled slots into the same available ground. -/
noncomputable def enumeratedSizedBlocksEquivEmbedding :
    EnumeratedSizedBlocks A p ≃ ((Σ i, Fin (p i)) ↪ A) :=
  Equiv.ofBijective enumeratedBlocksToEmbedding
    ⟨enumeratedBlocksToEmbedding_injective,
      fun g ↦ ⟨slotEmbeddingToEnumeratedBlocks g, enumeratedBlocksToEmbedding_slot_inverse g⟩⟩

theorem enumeratedSizedBlocks_card_embedding [Fintype ι] [Fintype α] :
    Fintype.card (EnumeratedSizedBlocks A p) = A.card.descFactorial (∑ i, p i) := by
  rw [Fintype.card_congr enumeratedSizedBlocksEquivEmbedding, Fintype.card_embedding_eq,
    Fintype.card_coe, Fintype.card_sigma]
  simp only [Fintype.card_fin]

theorem sizedDisjointBlocks_mul_factorials [Fintype ι] [Fintype α] :
    Fintype.card (SizedDisjointBlocks A p) * (∏ i, (p i).factorial) =
      A.card.descFactorial (∑ i, p i) :=
  (enumeratedSizedBlocks_count A p).symm.trans enumeratedSizedBlocks_card_embedding

/-- The paper's exact fixed-block-size coefficient. Every denominator
factor is earned by the injection count or the actual within-block fibres. -/
theorem sizedDisjointBlocks_count [Fintype ι] [Fintype α]
    (hp : (∑ i, p i) ≤ A.card) :
    Fintype.card (SizedDisjointBlocks A p) =
      A.card.factorial / ((A.card - ∑ i, p i).factorial * ∏ i, (p i).factorial) := by
  have hscaled :
      Fintype.card (SizedDisjointBlocks A p) *
        ((A.card - ∑ i, p i).factorial * ∏ i, (p i).factorial) = A.card.factorial := by
    calc
      _ = (A.card - ∑ i, p i).factorial *
          (Fintype.card (SizedDisjointBlocks A p) * ∏ i, (p i).factorial) := by ac_rfl
      _ = (A.card - ∑ i, p i).factorial * A.card.descFactorial (∑ i, p i) := by
        rw [sizedDisjointBlocks_mul_factorials]
      _ = A.card.factorial := Nat.factorial_mul_descFactorial hp
  have hpos : 0 < (A.card - ∑ i, p i).factorial * ∏ i, (p i).factorial :=
    Nat.mul_pos (Nat.factorial_pos _) (Finset.prod_pos (fun i _ ↦ Nat.factorial_pos (p i)))
  calc
    _ = (Fintype.card (SizedDisjointBlocks A p) *
        ((A.card - ∑ i, p i).factorial * ∏ i, (p i).factorial)) /
          ((A.card - ∑ i, p i).factorial * ∏ i, (p i).factorial) := (Nat.mul_div_cancel _ hpos).symm
    _ = _ := by rw [hscaled]

end BooleanAntichainsKernel
