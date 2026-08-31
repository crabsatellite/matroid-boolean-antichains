import BooleanAntichainsKernel.OrderedPartitionBlocks

namespace BooleanAntichainsKernel

open scoped Classical

theorem profiledBlocks_injective {n b : ℕ} (t : ProfiledOrderedBlocks n b) :
    Function.Injective t.1.2 := by
  intro i j hij
  by_contra hne
  have hd := t.2.2.2.2.2 hne
  have hself : Disjoint (t.1.2 j) (t.1.2 j) := by
    simpa only [hij] using hd
  have hempty : t.1.2 j = ∅ := disjoint_self.mp hself
  have hcard := t.2.2.2.2.1 j
  have hpos := t.2.2.1 j
  rw [hempty, Finset.card_empty] at hcard
  omega

theorem profiledBlocks_cover {n b : ℕ} (t : ProfiledOrderedBlocks n b) :
    (Finset.univ : Finset (Fin b)).biUnion t.1.2 = (Finset.univ : Finset (Fin n)) := by
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    exact Finset.mem_univ x
  · rw [Finset.card_biUnion (by
      intro i _hi j _hj hij
      exact t.2.2.2.2.2 hij)]
    simp_rw [t.2.2.2.2.1]
    rw [t.2.1, Finset.card_univ, Fintype.card_fin]

theorem profiledBlocks_existsUnique {n b : ℕ} (t : ProfiledOrderedBlocks n b) (x : Fin n) :
    ∃! C, C ∈ (Finset.univ : Finset (Fin b)).image t.1.2 ∧ x ∈ C := by
  have hx : x ∈ (Finset.univ : Finset (Fin b)).biUnion t.1.2 := by
    rw [profiledBlocks_cover]
    exact Finset.mem_univ x
  obtain ⟨i, _hi, hxi⟩ := Finset.mem_biUnion.mp hx
  refine ⟨t.1.2 i, ⟨Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩, hxi⟩, ?_⟩
  intro C hC
  obtain ⟨j, _hj, hjC⟩ := Finset.mem_image.mp hC.1
  subst C
  have hij : i = j := by
    by_contra hne
    exact (Finset.disjoint_left.mp (t.2.2.2.2.2 hne)) hxi hC.2
  rw [hij]

def profiledBlocksPartition {n b : ℕ} (t : ProfiledOrderedBlocks n b) :
    Finpartition (Finset.univ : Finset (Fin n)) :=
  Finpartition.ofExistsUnique ((Finset.univ : Finset (Fin b)).image t.1.2)
    (fun _ _ ↦ Finset.subset_univ _)
    (fun x _ ↦ profiledBlocks_existsUnique t x)
    (by
      intro h
      obtain ⟨i, _hi, hi⟩ := Finset.mem_image.mp h
      have hcard := t.2.2.2.2.1 i
      have hpos := t.2.2.1 i
      rw [hi, Finset.card_empty] at hcard
      omega)

theorem profiledBlocksPartition_parts {n b : ℕ} (t : ProfiledOrderedBlocks n b) :
    (profiledBlocksPartition t).parts = (Finset.univ : Finset (Fin b)).image t.1.2 := rfl

theorem profiledBlocksPartition_card {n b : ℕ} (t : ProfiledOrderedBlocks n b) :
    (profiledBlocksPartition t).parts.card = b := by
  rw [profiledBlocksPartition_parts,
    Finset.card_image_of_injective _ (profiledBlocks_injective t), Finset.card_univ, Fintype.card_fin]

noncomputable def profiledBlocksEnumeration {n b : ℕ} (t : ProfiledOrderedBlocks n b) :
    Fin b ≃ (profiledBlocksPartition t).parts :=
  Equiv.ofBijective
    (fun i ↦ ⟨t.1.2 i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩)
    ⟨fun i j h ↦ profiledBlocks_injective t (congrArg Subtype.val h),
      fun C ↦ by
        obtain ⟨i, _hi, hiC⟩ := Finset.mem_image.mp C.2
        exact ⟨i, Subtype.ext hiC⟩⟩

noncomputable def profiledBlocksToOrderedPartition {n b : ℕ} (t : ProfiledOrderedBlocks n b) :
    OrderedFinitePartition n b :=
  ⟨⟨profiledBlocksPartition t, profiledBlocksPartition_card t⟩,
    profiledBlocksEnumeration t⟩

theorem profiledBlocksToOrderedPartition_block {n b : ℕ} (t : ProfiledOrderedBlocks n b) (i : Fin b) :
    ((profiledBlocksToOrderedPartition t).2 i).1 = t.1.2 i := rfl

theorem orderedPartitionToProfiledBlocks_injective {n b : ℕ} :
    Function.Injective (orderedPartitionToProfiledBlocks :
      OrderedFinitePartition n b → ProfiledOrderedBlocks n b) := by
  rintro ⟨P, e⟩ ⟨Q, d⟩ h
  have hblocks : ∀ i, (e i).1 = (d i).1 := by
    intro i
    exact congrFun (congrArg (fun t : ProfiledOrderedBlocks n b ↦ t.1.2) h) i
  have hP : P = Q := by
    apply Subtype.ext
    apply Finpartition.ext
    ext C
    constructor
    · intro hC
      obtain ⟨i, hi⟩ := e.surjective ⟨C, hC⟩
      have hid : (e i).1 = C := congrArg Subtype.val hi
      rw [← hid, hblocks i]
      exact (d i).2
    · intro hC
      obtain ⟨i, hi⟩ := d.surjective ⟨C, hC⟩
      have hid : (d i).1 = C := congrArg Subtype.val hi
      rw [← hid, ← hblocks i]
      exact (e i).2
  subst Q
  have hed : e = d := by
    apply Equiv.ext
    intro i
    exact Subtype.ext (hblocks i)
  subst d
  rfl

theorem orderedPartitionToProfiledBlocks_surjective {n b : ℕ} :
    Function.Surjective (orderedPartitionToProfiledBlocks :
      OrderedFinitePartition n b → ProfiledOrderedBlocks n b) := by
  intro t
  refine ⟨profiledBlocksToOrderedPartition t, ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · funext i
    exact t.2.2.2.2.1 i
  · funext i
    rfl

/-- Exact two-sided equivalence: all original vertices, block
multiplicities, sizes and the explicit block ordering are retained. -/
noncomputable def orderedPartitionEquivProfiledBlocks (n b : ℕ) :
    OrderedFinitePartition n b ≃ ProfiledOrderedBlocks n b :=
  Equiv.ofBijective orderedPartitionToProfiledBlocks
    ⟨orderedPartitionToProfiledBlocks_injective,
      orderedPartitionToProfiledBlocks_surjective⟩

noncomputable instance (n b : ℕ) : Fintype (ProfiledOrderedBlocks n b) :=
  Fintype.ofEquiv (OrderedFinitePartition n b) (orderedPartitionEquivProfiledBlocks n b)

end BooleanAntichainsKernel
