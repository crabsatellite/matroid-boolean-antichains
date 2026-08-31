import BooleanAntichainsKernel.PartitionStirling
import BooleanAntichainsKernel.SizedBlockCoefficients
import Mathlib.Combinatorics.Enumerative.Bell

namespace BooleanAntichainsKernel

open scoped Classical

abbrev OrderedFinitePartition (n b : ℕ) :=
  Σ P : PartitionsWithBlocks (Fin n) b, Fin b ≃ P.1.parts

abbrev PositiveBlockProfile (n b : ℕ) :=
  {p : Fin b → ℕ // (∑ i, p i) = n ∧ ∀ i, 0 < p i}

abbrev ProfiledOrderedBlocks (n b : ℕ) :=
  {t : (Fin b → ℕ) × (Fin b → Finset (Fin n)) //
    (∑ i, t.1 i) = n ∧ (∀ i, 0 < t.1 i) ∧
      (∀ i, t.2 i ⊆ Finset.univ) ∧
      (∀ i, (t.2 i).card = t.1 i) ∧
      Pairwise fun i j ↦ Disjoint (t.2 i) (t.2 j)}

def orderedPartitionProfile {n b : ℕ} (t : OrderedFinitePartition n b) : PositiveBlockProfile n b :=
  ⟨fun i ↦ (t.2 i).1.card, by
    calc
      _ = ∑ B : t.1.1.parts, B.1.card :=
        t.2.sum_comp (fun B : t.1.1.parts ↦ B.1.card)
      _ = ∑ B ∈ t.1.1.parts, B.card :=
        Finset.sum_coe_sort t.1.1.parts (fun B : Finset (Fin n) ↦ B.card)
      _ = n := by simpa only [Finset.card_univ, Fintype.card_fin] using t.1.1.sum_card_parts,
    fun i ↦ Finset.card_pos.mpr (t.1.1.nonempty_of_mem_parts (t.2 i).2)⟩

def orderedPartitionBlocks {n b : ℕ} (t : OrderedFinitePartition n b) :
    SizedDisjointBlocks (Finset.univ : Finset (Fin n)) (orderedPartitionProfile t).1 :=
  ⟨fun i ↦ (t.2 i).1, fun _ ↦ Finset.subset_univ _,
    fun _ ↦ rfl, fun i j hij ↦ t.1.1.disjoint (t.2 i).2 (t.2 j).2
      (fun h ↦ hij (t.2.injective (Subtype.ext h)))⟩

def orderedPartitionToProfiledBlocks {n b : ℕ} (t : OrderedFinitePartition n b) :
    ProfiledOrderedBlocks n b :=
  ⟨((orderedPartitionProfile t).1, (orderedPartitionBlocks t).1),
    (orderedPartitionProfile t).2.1, (orderedPartitionProfile t).2.2,
    (orderedPartitionBlocks t).2.1, (orderedPartitionBlocks t).2.2.1,
    (orderedPartitionBlocks t).2.2.2⟩

theorem orderedPartitionToProfiledBlocks_profile {n b : ℕ} (t : OrderedFinitePartition n b) (i : Fin b) :
    (orderedPartitionToProfiledBlocks t).1.1 i = (t.2 i).1.card := rfl

theorem orderedPartitionToProfiledBlocks_block {n b : ℕ} (t : OrderedFinitePartition n b) (i : Fin b) :
    (orderedPartitionToProfiledBlocks t).1.2 i = (t.2 i).1 := rfl

theorem orderedPartition_weight {n b : ℕ} (t : OrderedFinitePartition n b) :
    (∏ i : Fin b, (Nat.bell ((orderedPartitionToProfiledBlocks t).1.1 i) : ℚ) ^ 2) =
      ∏ B : t.1.1.parts, (Nat.bell B.1.card : ℚ) ^ 2 := by
  exact t.2.prod_comp (fun B : t.1.1.parts ↦ (Nat.bell B.1.card : ℚ) ^ 2)

end BooleanAntichainsKernel
