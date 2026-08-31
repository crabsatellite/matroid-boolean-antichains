import BooleanAntichainsKernel.UniformBlockFaces
import BooleanAntichainsKernel.UniformFlats
import BooleanAntichainsKernel.TopBooleanHom

namespace BooleanAntichainsKernel

open Finset
open scoped Classical

variable {α : Type*} [Fintype α] [DecidableEq α]

namespace UniformBlockData

variable {E : Set α} {r k : ℕ}

noncomputable def toFlat (D : UniformBlockData E r k) (S : Finset (Fin k)) :
    MatroidFlat (uniformOn E r) :=
  ⟨(uniformOn E r).closure (uniformBlockFace D.bottom D.blocks S : Set α),
    (uniformOn E r).isFlat_closure _⟩

/-- Every proper face is the original ordinary union, not merely its closure. -/
theorem toFlat_val_of_proper (D : UniformBlockData E r k) (S : Finset (Fin k)) (hS : S ≠ univ) :
    (D.toFlat S).1 = (uniformBlockFace D.bottom D.blocks S : Set α) :=
  uniformOn_closure_of_card_lt E r _ (D.face_subset_ground S)
    (by simpa only [Set.ncard_coe_finset] using D.face_small S hS)

theorem toFlat_univ (D : UniformBlockData E r k) : D.toFlat univ = ⊤ := by
  apply Subtype.ext
  exact uniformOn_closure_of_rank_le E r _ (D.face_subset_ground univ)
    (by simpa only [Set.ncard_coe_finset] using D.full_rank)

theorem toFlat_union (D : UniformBlockData E r k) (S T : Finset (Fin k)) :
    D.toFlat (S ∪ T) = D.toFlat S ⊔ D.toFlat T := by
  apply Subtype.ext
  change (uniformOn E r).closure (uniformBlockFace D.bottom D.blocks (S ∪ T) : Set α) =
    (uniformOn E r).closure
      ((uniformOn E r).closure (uniformBlockFace D.bottom D.blocks S : Set α) ∪
       (uniformOn E r).closure (uniformBlockFace D.bottom D.blocks T : Set α))
  rw [uniformBlockFace_union, Finset.coe_union,
    Matroid.closure_closure_union_closure_eq_closure_union]

theorem toFlat_inter (D : UniformBlockData E r k) (S T : Finset (Fin k)) :
    D.toFlat (S ∩ T) = D.toFlat S ⊓ D.toFlat T := by
  by_cases hS : S = univ
  · subst S
    rw [Finset.univ_inter, toFlat_univ, top_inf_eq]
  by_cases hT : T = univ
  · subst T
    rw [Finset.inter_univ, toFlat_univ, inf_top_eq]
  have hST : S ∩ T ≠ univ := by
    intro h
    apply hS
    apply Finset.eq_univ_of_forall
    intro i
    exact (Finset.mem_inter.mp (h.symm ▸ Finset.mem_univ i)).1
  apply Subtype.ext
  rw [MatroidFlat.val_inf, toFlat_val_of_proper D S hS, toFlat_val_of_proper D T hT,
    toFlat_val_of_proper D (S ∩ T) hST,
    uniformBlockFace_inter D.bottom D.blocks D.blocks_pairwise, Finset.coe_inter]

theorem toFlat_injective (D : UniformBlockData E r k) : Function.Injective D.toFlat := by
  have hsub : ∀ {S T : Finset (Fin k)}, D.toFlat S = D.toFlat T → S ⊆ T := by
    intro S T h i hiS
    by_contra hiT
    have hT : T ≠ univ := fun hT ↦ hiT (hT.symm ▸ Finset.mem_univ i)
    obtain ⟨e, hei⟩ := D.blocks_nonempty i
    have heS : e ∈ uniformBlockFace D.bottom D.blocks S :=
      Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i, hiS, hei⟩)
    have heF : e ∈ (D.toFlat S).1 :=
      (uniformOn E r).subset_closure _ (D.face_subset_ground S) heS
    have heG : e ∈ (D.toFlat T).1 := by rw [← h]; exact heF
    rw [toFlat_val_of_proper D T hT] at heG
    rcases Finset.mem_union.mp heG with heX | heP
    · exact (Finset.disjoint_left.mp (D.bottom_disjoint i)) heX hei
    · rcases Finset.mem_biUnion.mp heP with ⟨j, hjT, hej⟩
      have hne : i ≠ j := fun hij ↦ hiT (hij.symm ▸ hjT)
      exact (Finset.disjoint_left.mp (D.blocks_pairwise hne)) hei hej
  exact fun _ _ h ↦ Finset.Subset.antisymm (hsub h) (hsub h.symm)

/-- The converse construction in the manuscript's uniform block proof.
The later bijection is restricted to k at least two as in that proof. -/
noncomputable def toEmbedding (D : UniformBlockData E r k) :
    TopBooleanEmbedding (Fin k) (MatroidFlat (uniformOn E r)) :=
  ⟨⟨D.toFlat, D.toFlat_union, D.toFlat_inter, D.toFlat_univ⟩, D.toFlat_injective⟩

end UniformBlockData
end BooleanAntichainsKernel
