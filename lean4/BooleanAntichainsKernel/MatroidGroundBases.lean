import BooleanAntichainsKernel.MatroidGroundFlats
import BooleanAntichainsKernel.TuttePolynomial
import Mathlib.Data.Finset.Image

namespace BooleanAntichainsKernel

open scoped Classical

variable {α R : Type*}

/-- Restore original labels without changing the finite basis or its multiplicities. -/
noncomputable def matroidGroundBasisToOriginal (M : Matroid α)
    (B : MatroidBases (M.restrictSubtype M.E)) : MatroidBases M :=
  ⟨B.1.map (Function.Embedding.subtype _), by
    rw [Finset.coe_map]
    exact (Matroid.restrictSubtype_ground_isBase_iff).mp B.2⟩

noncomputable def matroidGroundBasisFromOriginal (M : Matroid α)
    (B : MatroidBases M) : MatroidBases (M.restrictSubtype M.E) :=
  ⟨B.1.subtype (fun e ↦ e ∈ M.E), by
    apply Matroid.restrictSubtype_ground_isBase_iff.mpr
    have hmap := Finset.subtype_map_of_mem (fun e he ↦ B.2.subset_ground he)
    have hset : (Subtype.val : M.E → α) '' (↑(B.1.subtype (fun e ↦ e ∈ M.E)) : Set M.E) =
        (B.1 : Set α) := by
      exact (Finset.coe_map (Function.Embedding.subtype (fun e ↦ e ∈ M.E)) _).symm.trans
        (congrArg (fun S : Finset α ↦ (S : Set α)) hmap)
    rw [hset]
    exact B.2⟩

theorem matroidGroundBasis_left_inv (M : Matroid α)
    (B : MatroidBases (M.restrictSubtype M.E)) :
    matroidGroundBasisFromOriginal M (matroidGroundBasisToOriginal M B) = B := by
  apply Subtype.ext
  apply Finset.map_injective (Function.Embedding.subtype (fun e ↦ e ∈ M.E))
  exact Finset.subtype_map_of_mem (fun e he ↦ (matroidGroundBasisToOriginal M B).2.subset_ground he)

theorem matroidGroundBasis_right_inv (M : Matroid α) (B : MatroidBases M) :
    matroidGroundBasisToOriginal M (matroidGroundBasisFromOriginal M B) = B := by
  apply Subtype.ext
  exact Finset.subtype_map_of_mem (fun e he ↦ B.2.subset_ground he)

noncomputable def matroidGroundBasesEquiv (M : Matroid α) :
    MatroidBases (M.restrictSubtype M.E) ≃ MatroidBases M where
  toFun := matroidGroundBasisToOriginal M
  invFun := matroidGroundBasisFromOriginal M
  left_inv := matroidGroundBasis_left_inv M
  right_inv := matroidGroundBasis_right_inv M

theorem matroidGroundBasesEquiv_val (M : Matroid α) (B : MatroidBases (M.restrictSubtype M.E)) :
    (matroidGroundBasesEquiv M B).1 = B.1.map (Function.Embedding.subtype _) := rfl

theorem matroidGroundBasesEquiv_mem (M : Matroid α) (B : MatroidBases (M.restrictSubtype M.E))
    (e : M.E) : e.val ∈ (matroidGroundBasesEquiv M B).1 ↔ e ∈ B.1 := by
  rw [matroidGroundBasesEquiv_val, Finset.mem_map]
  constructor
  · rintro ⟨f, hf, hfe⟩
    exact (Subtype.ext hfe : f = e) ▸ hf
  · intro he
    exact ⟨e, he, rfl⟩

theorem matroidGroundBasesEquiv_card (M : Matroid α) (B : MatroidBases (M.restrictSubtype M.E)) :
    (matroidGroundBasesEquiv M B).1.card = B.1.card := Finset.card_map _

theorem matroidGroundBasesEquiv_prod [CommMonoid R] (M : Matroid α)
    (B : MatroidBases (M.restrictSubtype M.E)) (x : α → R) :
    (∏ e ∈ (matroidGroundBasesEquiv M B).1, x e) = ∏ e ∈ B.1, x e.val :=
  Finset.prod_map B.1 (Function.Embedding.subtype _) x

/-- Only the actual ground must be finite. -/
@[implicit_reducible] noncomputable def matroidGroundBasesFintype (M : Matroid α) [Fintype M.E] :
    Fintype (MatroidBases M) :=
  Fintype.ofEquiv (MatroidBases (M.restrictSubtype M.E)) (matroidGroundBasesEquiv M)

theorem matroidGroundBasesEquiv_sum [CommSemiring R] (M : Matroid α) [Fintype M.E]
    [Fintype (MatroidBases M)] (x : α → R) :
    (∑ B : MatroidBases M, ∏ e ∈ B.1, x e) =
      ∑ B : MatroidBases (M.restrictSubtype M.E), ∏ e ∈ B.1, x e.val := by
  have h := (matroidGroundBasesEquiv M).sum_comp (fun B : MatroidBases M ↦ ∏ e ∈ B.1, x e)
  simpa only [matroidGroundBasesEquiv_prod] using h.symm

end BooleanAntichainsKernel
