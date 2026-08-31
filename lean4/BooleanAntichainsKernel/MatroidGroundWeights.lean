import BooleanAntichainsKernel.MatroidGroundAntichains
import BooleanAntichainsKernel.MatroidGroundBases
import BooleanAntichainsKernel.BasisWeightExpansion

namespace BooleanAntichainsKernel

open scoped Classical

variable {α R : Type*}

/-- The literal nonloop part of an original flat, finite because the actual
ground is finite. No finiteness of the ambient label type is required. -/
noncomputable def matroidGroundParallelClassElements (M : Matroid α) [Finite M.E]
    (F : MatroidFlat M) : Finset α :=
  ((Set.toFinite M.E).subset (fun _ he ↦ F.2.subset_ground he.1 :
    F.1 \ M.loops ⊆ M.E)).toFinset

theorem matroidGroundParallelClassElements_mem (M : Matroid α) [Finite M.E]
    (F : MatroidFlat M) (e : α) :
    e ∈ matroidGroundParallelClassElements M F ↔ e ∈ F.1 \ M.loops :=
  Set.Finite.mem_toFinset _

theorem matroidGroundParallelClassElements_coe (M : Matroid α) [Finite M.E]
    (F : MatroidFlat M) :
    (matroidGroundParallelClassElements M F : Set α) = F.1 \ M.loops :=
  Set.Finite.coe_toFinset _

theorem matroidGroundParallelClassElements_eq [Fintype α] (M : Matroid α)
    (F : MatroidFlat M) : matroidGroundParallelClassElements M F = parallelClassElements F := by
  ext e
  rw [matroidGroundParallelClassElements_mem, mem_parallelClassElements]
  rfl

theorem matroidGroundParallelClassElements_map (M : Matroid α) [Fintype M.E]
    (F : MatroidFlat (M.restrictSubtype M.E)) :
    matroidGroundParallelClassElements M (matroidGroundFlatOrderIso M F) =
      (parallelClassElements F).map (Function.Embedding.subtype _) := by
  apply Finset.coe_injective
  rw [matroidGroundParallelClassElements_coe, Finset.coe_map]
  change (matroidGroundFlatOrderIso M F).1 \ M.loops =
    (Subtype.val : M.E → α) '' (↑(parallelClassElements F) : Set M.E)
  have hclass : (↑(parallelClassElements F) : Set M.E) =
      F.1 \ (M.restrictSubtype M.E).loops := by
    ext e
    exact mem_parallelClassElements F e
  rw [hclass]
  exact (matroidGround_parallelClassSet M F).symm

theorem matroidGroundParallelClassElements_sum [AddCommMonoid R] (M : Matroid α)
    [Fintype M.E] (F : MatroidFlat (M.restrictSubtype M.E)) (x : α → R) :
    (∑ e ∈ matroidGroundParallelClassElements M (matroidGroundFlatOrderIso M F), x e) =
      ∑ e ∈ parallelClassElements F, x e.val := by
  rw [matroidGroundParallelClassElements_map, Finset.sum_map]
  rfl

@[implicit_reducible] noncomputable def matroidGroundMaximumFintype (M : Matroid α) [Fintype M.E] :
    Fintype (BooleanAntichain (MatroidFlat.rank (⊤ : MatroidFlat M)) (MatroidFlat M)) :=
  Fintype.ofEquiv (MaximumBooleanAntichain (M.restrictSubtype M.E)) (matroidGroundMaximumEquiv M)

attribute [local instance 100] matroidGroundFlatFintype matroidGroundBasesFintype

theorem matroidGroundMaximumEquiv_spanAtoms (M : Matroid α) [Fintype M.E]
    (C : MaximumBooleanAntichain (M.restrictSubtype M.E)) :
    spanAtomFinset (matroidGroundMaximumEquiv M C).1 =
      mapFamily (matroidGroundFlatOrderIso M) (spanAtomFinset C.1) := by
  rw [matroidGroundMaximumEquiv_val]
  exact spanAtomFinset_mapFamily (matroidGroundFlatOrderIso M) C.1 C.2.2

theorem matroidGroundMaximumEquiv_weight [CommSemiring R] (M : Matroid α) [Fintype M.E]
    (C : MaximumBooleanAntichain (M.restrictSubtype M.E)) (x : α → R) :
    (∏ F ∈ spanAtomFinset (matroidGroundMaximumEquiv M C).1,
        ∑ e ∈ matroidGroundParallelClassElements M F, x e) =
      ∏ F ∈ antichainAtoms C.1, ∑ e ∈ parallelClassElements F, x e.val := by
  rw [matroidGroundMaximumEquiv_spanAtoms, spanAtomFinset_eq_antichainAtoms C.1 C.2.2]
  change (∏ F ∈ (antichainAtoms C.1).map (matroidGroundFlatOrderIso M).toEquiv.toEmbedding,
    ∑ e ∈ matroidGroundParallelClassElements M F, x e) = _
  rw [Finset.prod_map]
  apply Finset.prod_congr rfl
  intro F _hF
  exact matroidGroundParallelClassElements_sum M F x

/-- The existing weighted theorem, transported to the original flats,
actual Boolean-span atoms, original bases, and original label variables. -/
theorem finiteGround_weighted_basis_sum [CommSemiring R] (M : Matroid α) [Fintype M.E]
    (x : α → R) :
    (∑ B : MatroidBases M, ∏ e ∈ B.1, x e) =
      ∑ C : BooleanAntichain (MatroidFlat.rank (⊤ : MatroidFlat M)) (MatroidFlat M),
        ∏ F ∈ spanAtomFinset C.1, ∑ e ∈ matroidGroundParallelClassElements M F, x e := by
  rw [matroidGroundBasesEquiv_sum M x]
  rw [basisWeight_sum_maximum_antichains (M.restrictSubtype M.E) (fun e ↦ x e.val)]
  have h := (matroidGroundMaximumEquiv M).sum_comp
    (fun C ↦ ∏ F ∈ spanAtomFinset C.1, ∑ e ∈ matroidGroundParallelClassElements M F, x e)
  simpa only [matroidGroundMaximumEquiv_weight] using h

end BooleanAntichainsKernel
