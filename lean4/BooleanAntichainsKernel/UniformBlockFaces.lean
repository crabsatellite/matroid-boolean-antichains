import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod

namespace BooleanAntichainsKernel

open Finset
open scoped Classical

variable {α ι : Type*} [DecidableEq α] [DecidableEq ι]

/-- The literal ordinary union of the bottom and the selected blocks. -/
def uniformBlockFace (X : Finset α) (P : ι → Finset α) (S : Finset ι) : Finset α :=
  X ∪ S.biUnion P

omit [DecidableEq ι] in
@[simp] lemma uniformBlockFace_empty (X : Finset α) (P : ι → Finset α) :
    uniformBlockFace X P ∅ = X := by simp [uniformBlockFace]

omit [DecidableEq ι] in
lemma uniformBlockFace_mono (X : Finset α) (P : ι → Finset α)
    {S T : Finset ι} (hST : S ⊆ T) : uniformBlockFace X P S ⊆ uniformBlockFace X P T := by
  intro e he
  rcases Finset.mem_union.mp he with heX | heP
  · exact Finset.mem_union_left _ heX
  · rcases Finset.mem_biUnion.mp heP with ⟨i, hi, hei⟩
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i, hST hi, hei⟩)

lemma uniformBlockFace_union (X : Finset α) (P : ι → Finset α) (S T : Finset ι) :
    uniformBlockFace X P (S ∪ T) = uniformBlockFace X P S ∪ uniformBlockFace X P T := by
  simp [uniformBlockFace, Finset.union_biUnion, Finset.union_assoc, Finset.union_left_comm]

lemma uniformBlockFace_inter (X : Finset α) (P : ι → Finset α)
    (hP : Pairwise fun i j ↦ Disjoint (P i) (P j)) (S T : Finset ι) :
    uniformBlockFace X P (S ∩ T) = uniformBlockFace X P S ∩ uniformBlockFace X P T := by
  ext e
  simp only [uniformBlockFace, Finset.mem_union, Finset.mem_inter, Finset.mem_biUnion]
  constructor
  · rintro (heX | ⟨i, ⟨hiS, hiT⟩, hei⟩)
    · exact ⟨Or.inl heX, Or.inl heX⟩
    · exact ⟨Or.inr ⟨i, hiS, hei⟩, Or.inr ⟨i, hiT, hei⟩⟩
  · rintro ⟨heS, heT⟩
    rcases heS with heX | ⟨i, hiS, hei⟩
    · exact Or.inl heX
    rcases heT with heX | ⟨j, hjT, hej⟩
    · exact Or.inl heX
    have hij : i = j := by
      by_contra hne
      exact (Finset.disjoint_left.mp (hP hne)) hei hej
    subst j
    exact Or.inr ⟨i, ⟨hiS, hjT⟩, hei⟩

/-- Actual bottom and ordered blocks from the proof of thm:uniform-all.
The full union need not be the ground set: unused elements are permitted.
Only the full-join rank threshold and proper-coatom bounds are required. -/
structure UniformBlockData (E : Set α) (r k : ℕ) where
  bottom : Finset α
  blocks : Fin k → Finset α
  bottom_subset : (bottom : Set α) ⊆ E
  blocks_subset : ∀ i, (blocks i : Set α) ⊆ E
  bottom_disjoint : ∀ i, Disjoint bottom (blocks i)
  blocks_pairwise : Pairwise fun i j ↦ Disjoint (blocks i) (blocks j)
  blocks_nonempty : ∀ i, (blocks i).Nonempty
  bottom_small : bottom.card < r
  full_rank : r ≤ (uniformBlockFace bottom blocks univ).card
  coatom_small : ∀ i, (uniformBlockFace bottom blocks (univ.erase i)).card < r

lemma uniformBlockData_ext {E : Set α} {r k : ℕ} {D G : UniformBlockData E r k}
    (hbottom : D.bottom = G.bottom) (hblocks : D.blocks = G.blocks) : D = G := by
  cases D
  cases G
  cases hbottom
  cases hblocks
  rfl

noncomputable instance [Fintype α] (E : Set α) (r k : ℕ) : Fintype (UniformBlockData E r k) :=
  Fintype.ofInjective (fun D : UniformBlockData E r k ↦ (D.bottom, D.blocks))
    (fun _ _ h ↦ uniformBlockData_ext (congrArg Prod.fst h) (congrArg Prod.snd h))

namespace UniformBlockData

variable {E : Set α} {r k : ℕ}

lemma face_subset_ground (D : UniformBlockData E r k) (S : Finset (Fin k)) :
    (uniformBlockFace D.bottom D.blocks S : Set α) ⊆ E := by
  intro e he
  rcases Finset.mem_union.mp he with heX | heP
  · exact D.bottom_subset heX
  · rcases Finset.mem_biUnion.mp heP with ⟨i, _, hei⟩
    exact D.blocks_subset i hei

lemma face_small (D : UniformBlockData E r k) (S : Finset (Fin k)) (hS : S ≠ univ) :
    (uniformBlockFace D.bottom D.blocks S).card < r := by
  have hn : ¬ ∀ i, i ∈ S := fun h ↦ hS (Finset.eq_univ_of_forall h)
  obtain ⟨i, hi⟩ := not_forall.mp hn
  have hsub : S ⊆ univ.erase i := by
    intro j hj
    exact Finset.mem_erase.mpr ⟨fun hji ↦ hi (hji ▸ hj), Finset.mem_univ j⟩
  exact (Finset.card_le_card (uniformBlockFace_mono D.bottom D.blocks hsub)).trans_lt (D.coatom_small i)

end UniformBlockData
end BooleanAntichainsKernel
