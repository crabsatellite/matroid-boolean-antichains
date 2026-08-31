import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace BooleanAntichainsKernel

open Finset
open scoped Classical

variable {ι α : Type*}

/-- Actual ordered disjoint subsets of a fixed available ground, with the
specified block cardinalities. Zero sizes are allowed in this counting
foundation; the uniform theorem separately filters to positive sizes. -/
abbrev SizedDisjointBlocks (A : Finset α) (p : ι → ℕ) :=
  {P : ι → Finset α //
    (∀ i, P i ⊆ A) ∧ (∀ i, (P i).card = p i) ∧
      Pairwise fun i j ↦ Disjoint (P i) (P j)}

noncomputable instance [Fintype ι] [Fintype α] (A : Finset α) (p : ι → ℕ) :
    Fintype (SizedDisjointBlocks A p) := Subtype.fintype _

abbrev SizedBlockEnumeration {A : Finset α} {p : ι → ℕ} (B : SizedDisjointBlocks A p) :=
  (i : ι) → (Fin (p i) ≃ ↥(B.1 i))

abbrev EnumeratedSizedBlocks (A : Finset α) (p : ι → ℕ) :=
  Σ B : SizedDisjointBlocks A p, SizedBlockEnumeration B

noncomputable def sizedBlockCanonicalEquiv {A : Finset α} {p : ι → ℕ}
    (B : SizedDisjointBlocks A p) (i : ι) : Fin (p i) ≃ ↥(B.1 i) :=
  (Finset.equivFinOfCardEq (B.2.2.1 i)).symm

/-- Give every element in every actual block its own labelled slot. -/
def enumeratedBlocksToEmbedding {A : Finset α} {p : ι → ℕ}
    (x : EnumeratedSizedBlocks A p) : (Σ i, Fin (p i)) ↪ A where
  toFun u := ⟨((x.2 u.1) u.2).1, x.1.2.1 u.1 ((x.2 u.1) u.2).2⟩
  inj' := by
    rintro ⟨i, a⟩ ⟨j, b⟩ h
    have hv : ((x.2 i) a).1 = ((x.2 j) b).1 := congrArg Subtype.val h
    have hij : i = j := by
      by_contra hne
      have hj : ((x.2 i) a).1 ∈ x.1.1 j := hv.symm ▸ ((x.2 j) b).2
      exact (Finset.disjoint_left.mp (x.1.2.2.2 hne)) ((x.2 i) a).2 hj
    subst j
    have hab : a = b := (x.2 i).injective (Subtype.ext hv)
    exact congrArg (Sigma.mk i) hab

lemma enumeratedBlocks_subset_of_embedding_eq {A : Finset α} {p : ι → ℕ}
    {x y : EnumeratedSizedBlocks A p}
    (h : enumeratedBlocksToEmbedding x = enumeratedBlocksToEmbedding y) (i : ι) :
    x.1.1 i ⊆ y.1.1 i := by
  intro z hz
  obtain ⟨j, hj⟩ := (x.2 i).surjective ⟨z, hz⟩
  have hxy := congrArg (fun g : (Σ i, Fin (p i)) ↪ A ↦ (g ⟨i, j⟩).1) h
  change ((x.2 i) j).1 = ((y.2 i) j).1 at hxy
  have hz' : z = ((y.2 i) j).1 := (congrArg Subtype.val hj).symm.trans hxy
  rw [hz']
  exact ((y.2 i) j).2

theorem enumeratedBlocksToEmbedding_injective {A : Finset α} {p : ι → ℕ} :
    Function.Injective (enumeratedBlocksToEmbedding (A := A) (p := p)) := by
  rintro ⟨B, e⟩ ⟨C, d⟩ h
  have hBC : B = C := Subtype.ext (funext fun i ↦ Finset.Subset.antisymm
    (enumeratedBlocks_subset_of_embedding_eq h i) (enumeratedBlocks_subset_of_embedding_eq h.symm i))
  cases hBC
  apply congrArg (Sigma.mk B)
  funext i
  apply Equiv.ext
  intro j
  apply Subtype.ext
  exact congrArg (fun g : (Σ i, Fin (p i)) ↪ A ↦ (g ⟨i, j⟩).1) h

theorem sizedBlockEnumeration_count [Fintype ι] {A : Finset α} {p : ι → ℕ}
    (B : SizedDisjointBlocks A p) :
    Fintype.card (SizedBlockEnumeration B) = ∏ i, (p i).factorial := by
  rw [Fintype.card_pi]
  apply Finset.prod_congr rfl
  intro i _
  simpa using Fintype.card_equiv (sizedBlockCanonicalEquiv B i)

/-- Count the independent within-block label permutations as actual fibres. -/
theorem enumeratedSizedBlocks_count [Fintype ι] [Fintype α] (A : Finset α) (p : ι → ℕ) :
    Fintype.card (EnumeratedSizedBlocks A p) =
      Fintype.card (SizedDisjointBlocks A p) * ∏ i, (p i).factorial := by
  rw [Fintype.card_sigma]
  simp_rw [sizedBlockEnumeration_count]
  simp

end BooleanAntichainsKernel
