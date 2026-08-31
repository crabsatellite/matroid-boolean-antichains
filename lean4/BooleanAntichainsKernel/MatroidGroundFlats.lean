import BooleanAntichainsKernel.MatroidRank
import Mathlib.Combinatorics.Matroid.Map

namespace BooleanAntichainsKernel

open scoped Classical

variable {α : Type*}

theorem matroidGround_image_preimage (M : Matroid α) (X : Set α) (hX : X ⊆ M.E) :
    (Subtype.val : M.E → α) '' ((Subtype.val : M.E → α) ⁻¹' X) = X := by
  ext x
  constructor
  · rintro ⟨e, he, rfl⟩
    exact he
  · intro hx
    exact ⟨⟨x, hX hx⟩, hx, rfl⟩

theorem matroidGround_preimage_image (M : Matroid α) (X : Set M.E) :
    (Subtype.val : M.E → α) ⁻¹' ((Subtype.val : M.E → α) '' X) = X := by
  ext x
  constructor
  · rintro ⟨y, hy, hyx⟩
    exact (Subtype.ext hyx : y = x) ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- The native ground restriction has exactly the original closure,
pulled back along the identity-on-labels subtype inclusion. -/
theorem matroidGround_closure (M : Matroid α) (X : Set M.E) :
    (M.restrictSubtype M.E).closure X =
      (Subtype.val : M.E → α) ⁻¹' M.closure ((Subtype.val : M.E → α) '' X) := by
  rw [Matroid.restrictSubtype, Matroid.restrict_ground_eq_self, Matroid.comap_closure_eq]

theorem matroidGround_image_isFlat (M : Matroid α) (F : MatroidFlat (M.restrictSubtype M.E)) :
    M.IsFlat ((Subtype.val : M.E → α) '' F.1) := by
  apply Matroid.isFlat_iff_closure_eq.mpr
  apply Set.Subset.antisymm
  · intro e he
    let ee : M.E := ⟨e, M.closure_subset_ground _ he⟩
    have hee : ee ∈ (M.restrictSubtype M.E).closure F.1 := by
      rw [matroidGround_closure]
      exact he
    rw [F.2.closure] at hee
    exact ⟨ee, hee, rfl⟩
  · exact M.subset_closure _ (by
      rintro _ ⟨e, _he, rfl⟩
      exact e.2)

theorem matroidGround_preimage_isFlat (M : Matroid α) (F : MatroidFlat M) :
    (M.restrictSubtype M.E).IsFlat ((Subtype.val : M.E → α) ⁻¹' F.1) := by
  apply Matroid.isFlat_iff_closure_eq.mpr
  rw [matroidGround_closure, matroidGround_image_preimage M F.1 F.2.subset_ground, F.2.closure]

/-- A lattice order isomorphism on the literal flat sets. The forward
map restores original labels; the inverse adds only ground-membership proofs. -/
def matroidGroundFlatOrderIso (M : Matroid α) :
    MatroidFlat (M.restrictSubtype M.E) ≃o MatroidFlat M where
  toFun F := ⟨(Subtype.val : M.E → α) '' F.1, matroidGround_image_isFlat M F⟩
  invFun F := ⟨(Subtype.val : M.E → α) ⁻¹' F.1, matroidGround_preimage_isFlat M F⟩
  left_inv F := Subtype.ext (matroidGround_preimage_image M F.1)
  right_inv F := Subtype.ext (matroidGround_image_preimage M F.1 F.2.subset_ground)
  map_rel_iff' := by
    intro F H
    change ((Subtype.val : M.E → α) '' F.1 ⊆ (Subtype.val : M.E → α) '' H.1) ↔ F.1 ⊆ H.1
    exact Set.image_subset_image_iff Subtype.val_injective

theorem matroidGroundFlatOrderIso_val (M : Matroid α) (F : MatroidFlat (M.restrictSubtype M.E)) :
    (matroidGroundFlatOrderIso M F).1 = (Subtype.val : M.E → α) '' F.1 := rfl

theorem matroidGroundFlatOrderIso_symm_val (M : Matroid α) (F : MatroidFlat M) :
    ((matroidGroundFlatOrderIso M).symm F).1 = (Subtype.val : M.E → α) ⁻¹' F.1 := rfl

theorem matroidGround_rank (M : Matroid α) (X : Set M.E) :
    matroidRank (M.restrictSubtype M.E) X = matroidRank M ((Subtype.val : M.E → α) '' X) := by
  unfold matroidRank
  rw [Matroid.restrictSubtype, Matroid.restrict_ground_eq_self, Matroid.eRk_comap]

theorem matroidGroundFlatOrderIso_rank (M : Matroid α) (F : MatroidFlat (M.restrictSubtype M.E)) :
    MatroidFlat.rank (matroidGroundFlatOrderIso M F) = MatroidFlat.rank F :=
  (matroidGround_rank M F.1).symm

/-- Finiteness is obtained from the actual ground, not the ambient type. -/
@[implicit_reducible] noncomputable def matroidGroundFlatFintype (M : Matroid α) [Fintype M.E] : Fintype (MatroidFlat M) :=
  Fintype.ofEquiv (MatroidFlat (M.restrictSubtype M.E)) (matroidGroundFlatOrderIso M).toEquiv

end BooleanAntichainsKernel
