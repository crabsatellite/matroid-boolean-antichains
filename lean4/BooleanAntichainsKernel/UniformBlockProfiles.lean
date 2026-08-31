import BooleanAntichainsKernel.UniformBlockFaces
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Set.Card

namespace BooleanAntichainsKernel

open Finset
open scoped Classical

variable {α ι : Type*} [DecidableEq α]

theorem uniformBlockFace_card_of_disjoint (X : Finset α) (P : ι → Finset α)
    (hX : ∀ i, Disjoint X (P i)) (hP : Pairwise fun i j ↦ Disjoint (P i) (P j))
    (S : Finset ι) :
    (uniformBlockFace X P S).card = X.card + ∑ i ∈ S, (P i).card := by
  unfold uniformBlockFace
  rw [Finset.card_union_of_disjoint
    ((Finset.disjoint_biUnion_right X S P).mpr (fun i _ ↦ hX i))]
  rw [Finset.card_biUnion (by intro i _ j _ hij; exact hP hij)]

/-- The precise finite arithmetic constraints in eq:uniform-all, including
unused elements and the separate proper-coatom inequalities. -/
def UniformProfileValid (n r k b : ℕ) (p : Fin k → ℕ) : Prop :=
  b < r ∧ (∀ i, 1 ≤ p i) ∧ (∑ i, p i) ≤ n - b ∧
    r ≤ b + ∑ i, p i ∧ ∀ i, (b + ∑ j, p j) - p i < r

namespace UniformBlockData

variable {E : Set α} {r k : ℕ}

theorem face_card (D : UniformBlockData E r k) (S : Finset (Fin k)) :
    (uniformBlockFace D.bottom D.blocks S).card =
      D.bottom.card + ∑ i ∈ S, (D.blocks i).card :=
  uniformBlockFace_card_of_disjoint D.bottom D.blocks D.bottom_disjoint D.blocks_pairwise S

theorem coatom_card (D : UniformBlockData E r k) (i : Fin k) :
    (uniformBlockFace D.bottom D.blocks (univ.erase i)).card =
      (D.bottom.card + ∑ j, (D.blocks j).card) - (D.blocks i).card := by
  rw [D.face_card]
  have hs := Finset.sum_erase_add univ (fun j ↦ (D.blocks j).card) (Finset.mem_univ i)
  omega

theorem profile_valid [Fintype α] (D : UniformBlockData E r k) :
    UniformProfileValid E.ncard r k D.bottom.card (fun i ↦ (D.blocks i).card) := by
  refine ⟨D.bottom_small, fun i ↦ Nat.succ_le_iff.mpr (Finset.card_pos.mpr (D.blocks_nonempty i)),
    ?_, ?_, ?_⟩
  · dsimp only
    have hg := Set.ncard_le_ncard (D.face_subset_ground univ)
    rw [Set.ncard_coe_finset, D.face_card] at hg
    omega
  · simpa only [D.face_card] using D.full_rank
  · intro i
    simpa only [D.coatom_card] using D.coatom_small i

end UniformBlockData

/-- Conversely, the displayed arithmetic constraints recover exactly the
rank conditions on the actual disjoint block family. -/
def uniformBlockDataOfProfile [Fintype α] {E : Set α} {r k : ℕ}
    (X : Finset α) (P : Fin k → Finset α)
    (hXE : (X : Set α) ⊆ E) (hPE : ∀ i, (P i : Set α) ⊆ E)
    (hX : ∀ i, Disjoint X (P i)) (hP : Pairwise fun i j ↦ Disjoint (P i) (P j))
    (hp : UniformProfileValid E.ncard r k X.card (fun i ↦ (P i).card)) :
    UniformBlockData E r k where
  bottom := X
  blocks := P
  bottom_subset := hXE
  blocks_subset := hPE
  bottom_disjoint := hX
  blocks_pairwise := hP
  blocks_nonempty i := Finset.card_pos.mp (Nat.succ_le_iff.mp (hp.2.1 i))
  bottom_small := hp.1
  full_rank := by
    rw [uniformBlockFace_card_of_disjoint X P hX hP]
    exact hp.2.2.2.1
  coatom_small i := by
    rw [uniformBlockFace_card_of_disjoint X P hX hP]
    have hs := Finset.sum_erase_add univ (fun j ↦ (P j).card) (Finset.mem_univ i)
    have hi := hp.2.2.2.2 i
    dsimp only at hi
    omega

end BooleanAntichainsKernel
