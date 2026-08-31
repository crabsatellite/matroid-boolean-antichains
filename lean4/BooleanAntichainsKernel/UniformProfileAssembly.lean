import BooleanAntichainsKernel.UniformProfileIndex

namespace BooleanAntichainsKernel

open Finset
open scoped Classical

variable {α : Type*} [Fintype α] [DecidableEq α] {E : Set α} {r k : ℕ}

noncomputable def uniformDecompositionToBlocks (d : UniformBlockDecomposition E r k) :
    UniformBlockData E r k := by
  let X := d.1
  let p := d.2.1
  let B := d.2.2
  have hXE : (X.1 : Set α) ⊆ E := fun e he ↦ Set.mem_toFinset.mp (X.2.1 he)
  have hPE : ∀ i, (B.1 i : Set α) ⊆ E := by
    intro i e he
    exact ((mem_blockAvailableGround E X.1 e).mp (B.2.1 i he)).1
  have hdis : ∀ i, Disjoint X.1 (B.1 i) := by
    intro i
    apply Finset.disjoint_left.mpr
    intro e heX heP
    exact ((mem_blockAvailableGround E X.1 e).mp (B.2.1 i heP)).2 heX
  have hprofile : UniformProfileValid E.ncard r k X.1.card (fun i ↦ (B.1 i).card) := by
    have hc : (fun i ↦ (B.1 i).card) = p.1 := funext B.2.2.1
    rw [hc]
    exact p.2
  exact uniformBlockDataOfProfile X.1 B.1 hXE hPE hdis B.2.2.2 hprofile

noncomputable def uniformBlocksToDecomposition (D : UniformBlockData E r k) :
    UniformBlockDecomposition E r k := by
  let X : SmallGroundSubsets E r := ⟨D.bottom,
    fun e he ↦ Set.mem_toFinset.mpr (D.bottom_subset he), D.bottom_small⟩
  let p : UniformAdmissibleProfile E.ncard r k X.1.card :=
    ⟨fun i ↦ (D.blocks i).card, D.profile_valid⟩
  let B : SizedDisjointBlocks (blockAvailableGround E X.1) p.1 := ⟨D.blocks, by
    intro i e he
    apply (mem_blockAvailableGround E X.1 e).mpr
    refine ⟨D.blocks_subset i he, ?_⟩
    intro heX
    exact (Finset.disjoint_left.mp (D.bottom_disjoint i)) heX he,
    fun _ ↦ rfl, D.blocks_pairwise⟩
  exact ⟨X, p, B⟩

theorem uniformDecomposition_blocks_roundtrip (D : UniformBlockData E r k) :
    uniformDecompositionToBlocks (uniformBlocksToDecomposition D) = D := by
  apply uniformBlockData_ext <;> rfl

theorem uniformDecompositionToBlocks_injective :
    Function.Injective (uniformDecompositionToBlocks (E := E) (r := r) (k := k)) := by
  rintro ⟨X, p, B⟩ ⟨Y, q, C⟩ h
  have hXY : X = Y :=
    Subtype.ext (congrArg (fun D : UniformBlockData E r k ↦ D.bottom) h)
  cases hXY
  have hblocks : B.1 = C.1 := congrArg (fun D : UniformBlockData E r k ↦ D.blocks) h
  have hpq : p = q := by
    apply Subtype.ext
    funext i
    exact (B.2.2.1 i).symm.trans
      ((congrArg (fun P : Fin k → Finset α ↦ (P i).card) hblocks).trans (C.2.2.1 i))
  cases hpq
  have hBC : B = C := Subtype.ext hblocks
  cases hBC
  rfl

/-- The decomposition is indexed by the actual bottom and the actual
cardinalities of the blocks. It is not an assumed count partition. -/
noncomputable def uniformProfileDecompositionEquiv :
    UniformBlockDecomposition E r k ≃ UniformBlockData E r k :=
  Equiv.ofBijective uniformDecompositionToBlocks
    ⟨uniformDecompositionToBlocks_injective,
      fun D ↦ ⟨uniformBlocksToDecomposition D, uniformDecomposition_blocks_roundtrip D⟩⟩

theorem uniformBlocksToDecomposition_index (D : UniformBlockData E r k) :
    (uniformBlocksToDecomposition D).1.1 = D.bottom ∧
      (uniformBlocksToDecomposition D).2.1.1 = (fun i ↦ (D.blocks i).card) :=
  ⟨rfl, rfl⟩

end BooleanAntichainsKernel
