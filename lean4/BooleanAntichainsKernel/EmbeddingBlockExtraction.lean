import BooleanAntichainsKernel.ActiveAtoms
import BooleanAntichainsKernel.SimplifiedBasis
import BooleanAntichainsKernel.UniformBlockFaces

namespace BooleanAntichainsKernel

open Set Finset
open scoped Classical

lemma topHom_eq_bottom_sup_singletons {ι L : Type*} [Fintype ι] [DecidableEq ι]
    [Lattice L] [OrderBot L] [OrderTop L] (f : TopBooleanHom ι L) (S : Finset ι) :
    f.1 S = f.1 ∅ ⊔ S.sup (fun i ↦ f.1 {i}) := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S _ ih =>
    rw [topBooleanHom_insert, Finset.sup_insert, ih]
    ac_rfl

variable {α : Type*} [Fintype α] {M : Matroid α} {k : ℕ}

omit [Fintype α] in
lemma flatTopHom_union_atoms (f : TopBooleanHom (Fin k) (MatroidFlat M)) (S : Finset (Fin k)) :
    (f.1 S).1 = M.closure ((f.1 ∅).1 ∪ ⋃ i ∈ S, (f.1 {i}).1) := by
  rw [topHom_eq_bottom_sup_singletons f S]
  change M.closure ((f.1 ∅).1 ∪ (S.sup (fun i ↦ f.1 {i})).1) = _
  rw [flat_finset_sup_coe, Matroid.closure_union_closure_right_eq]

noncomputable def embeddingBlockBottom (f : TopBooleanEmbedding (Fin k) (MatroidFlat M)) : Finset α :=
  (f.1.1 ∅).1.toFinset

noncomputable def embeddingBlocks (f : TopBooleanEmbedding (Fin k) (MatroidFlat M))
    (i : Fin k) : Finset α :=
  ((f.1.1 {i}).1 \ (f.1.1 ∅).1).toFinset

lemma embeddingBlockFace_coe [DecidableEq α]
    (f : TopBooleanEmbedding (Fin k) (MatroidFlat M)) (S : Finset (Fin k)) :
    (uniformBlockFace (embeddingBlockBottom f) (embeddingBlocks f) S : Set α) =
      (f.1.1 ∅).1 ∪ ⋃ i ∈ S, (f.1.1 {i}).1 := by
  ext e
  by_cases he : e ∈ (f.1.1 ∅).1 <;>
    simp [uniformBlockFace, embeddingBlockBottom, embeddingBlocks, he]

/-- Reconstruct every actual matroid-flat image as the closure of the
literal bottom and atom differences. Uniformity will remove closure only
on proper faces. -/
theorem embedding_face_eq_closure_blocks [DecidableEq α]
    (f : TopBooleanEmbedding (Fin k) (MatroidFlat M))
    (S : Finset (Fin k)) :
    (f.1.1 S).1 = M.closure (uniformBlockFace (embeddingBlockBottom f) (embeddingBlocks f) S : Set α) :=
  (flatTopHom_union_atoms f.1 S).trans (congrArg M.closure (embeddingBlockFace_coe f S).symm)

omit [Fintype α] in
lemma embeddingBottom_subset_atom (f : TopBooleanEmbedding (Fin k) (MatroidFlat M)) (i : Fin k) :
    (f.1.1 ∅).1 ⊆ (f.1.1 {i}).1 :=
  topBooleanHom_mono f.1 (Finset.empty_subset {i})

lemma embeddingBlockBottom_subset_ground (f : TopBooleanEmbedding (Fin k) (MatroidFlat M)) :
    (embeddingBlockBottom f : Set α) ⊆ M.E := by
  intro e he
  exact (f.1.1 ∅).2.subset_ground (Set.mem_toFinset.mp he)

lemma embeddingBlocks_subset_ground (f : TopBooleanEmbedding (Fin k) (MatroidFlat M)) (i : Fin k) :
    (embeddingBlocks f i : Set α) ⊆ M.E := by
  intro e he
  exact (f.1.1 {i}).2.subset_ground (Set.mem_toFinset.mp he).1

lemma embeddingBlocks_disjoint_bottom (f : TopBooleanEmbedding (Fin k) (MatroidFlat M)) (i : Fin k) :
    Disjoint (embeddingBlockBottom f) (embeddingBlocks f i) := by
  apply Finset.disjoint_left.mpr
  intro e heX heP
  exact (Set.mem_toFinset.mp heP).2 (Set.mem_toFinset.mp heX)

theorem embeddingBlocks_nonempty (f : TopBooleanEmbedding (Fin k) (MatroidFlat M)) (i : Fin k) :
    (embeddingBlocks f i).Nonempty := by
  have hnot : ¬ (f.1.1 {i}).1 ⊆ (f.1.1 ∅).1 := by
    intro h
    have heq : f.1.1 {i} = f.1.1 ∅ :=
      Subtype.ext (Set.Subset.antisymm h (embeddingBottom_subset_atom f i))
    have hc := f.2 heq
    simp at hc
  obtain ⟨e, heA, heX⟩ := Set.not_subset.mp hnot
  exact ⟨e, Set.mem_toFinset.mpr ⟨heA, heX⟩⟩

theorem embeddingBlocks_pairwise (f : TopBooleanEmbedding (Fin k) (MatroidFlat M)) :
    Pairwise fun i j ↦ Disjoint (embeddingBlocks f i) (embeddingBlocks f j) := by
  intro i j hij
  apply Finset.disjoint_left.mpr
  intro e hei hej
  have hi := Set.mem_toFinset.mp hei
  have hj := Set.mem_toFinset.mp hej
  have hnot : i ∉ ({j} : Finset (Fin k)) := by simpa using hij
  have hmeet := f.1.2.2.1 {i} {j}
  rw [Finset.singleton_inter_of_notMem hnot] at hmeet
  have hval := congrArg Subtype.val hmeet
  rw [MatroidFlat.val_inf] at hval
  apply hi.2
  rw [hval]
  exact ⟨hi.1, hj.1⟩

end BooleanAntichainsKernel
