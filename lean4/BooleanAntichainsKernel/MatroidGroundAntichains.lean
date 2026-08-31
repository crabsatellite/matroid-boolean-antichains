import BooleanAntichainsKernel.MatroidGroundFlats
import BooleanAntichainsKernel.LatticeTransport
import BooleanAntichainsKernel.MatroidSimplification
import Mathlib.Combinatorics.Matroid.Loop

namespace BooleanAntichainsKernel

open scoped Classical

variable {α : Type*} (M : Matroid α)

section Antichains

variable [DecidableEq (MatroidFlat M)]
  [DecidableEq (MatroidFlat (M.restrictSubtype M.E))]

noncomputable def matroidGroundAntichainEquiv (k : ℕ) :
    BooleanAntichain k (MatroidFlat (M.restrictSubtype M.E)) ≃ BooleanAntichain k (MatroidFlat M) :=
  booleanAntichainOrderIsoEquiv (matroidGroundFlatOrderIso M) k

theorem matroidGroundAntichainEquiv_val (k : ℕ)
    (C : BooleanAntichain k (MatroidFlat (M.restrictSubtype M.E))) :
    (matroidGroundAntichainEquiv M k C).1 = mapFamily (matroidGroundFlatOrderIso M) C.1 := rfl

theorem matroidGroundAntichainEquiv_atoms (k : ℕ)
    (C : BooleanAntichain k (MatroidFlat (M.restrictSubtype M.E))) :
    antichainAtoms (matroidGroundAntichainEquiv M k C).1 =
      mapFamily (matroidGroundFlatOrderIso M) (antichainAtoms C.1) :=
  antichainAtoms_mapFamily (matroidGroundFlatOrderIso M) C.1

omit [DecidableEq (MatroidFlat M)] [DecidableEq (MatroidFlat (M.restrictSubtype M.E))] in
theorem matroidGround_top_rank :
    MatroidFlat.rank (⊤ : MatroidFlat (M.restrictSubtype M.E)) = MatroidFlat.rank (⊤ : MatroidFlat M) := by
  simpa only [map_top] using (matroidGroundFlatOrderIso_rank M (⊤ : MatroidFlat (M.restrictSubtype M.E))).symm

noncomputable def matroidGroundMaximumEquiv :
    BooleanAntichain (MatroidFlat.rank (⊤ : MatroidFlat (M.restrictSubtype M.E)))
      (MatroidFlat (M.restrictSubtype M.E)) ≃
    BooleanAntichain (MatroidFlat.rank (⊤ : MatroidFlat M)) (MatroidFlat M) :=
  (matroidGroundAntichainEquiv M _).trans (booleanAntichainSizeEquiv (matroidGround_top_rank M))

theorem matroidGroundMaximumEquiv_val
    (C : BooleanAntichain (MatroidFlat.rank (⊤ : MatroidFlat (M.restrictSubtype M.E)))
      (MatroidFlat (M.restrictSubtype M.E))) :
    (matroidGroundMaximumEquiv M C).1 = mapFamily (matroidGroundFlatOrderIso M) C.1 := rfl

theorem matroidGroundMaximumEquiv_atoms
    (C : BooleanAntichain (MatroidFlat.rank (⊤ : MatroidFlat (M.restrictSubtype M.E)))
      (MatroidFlat (M.restrictSubtype M.E))) :
    antichainAtoms (matroidGroundMaximumEquiv M C).1 =
      mapFamily (matroidGroundFlatOrderIso M) (antichainAtoms C.1) :=
  antichainAtoms_mapFamily (matroidGroundFlatOrderIso M) C.1

end Antichains

noncomputable def matroidGroundRankOneEquiv :
    RankOneFlat (M.restrictSubtype M.E) ≃ RankOneFlat M :=
  Equiv.subtypeEquiv (matroidGroundFlatOrderIso M).toEquiv (fun F ↦ by
    change MatroidFlat.rank F = 1 ↔ MatroidFlat.rank (matroidGroundFlatOrderIso M F) = 1
    rw [matroidGroundFlatOrderIso_rank])

theorem matroidGroundRankOneEquiv_val (F : RankOneFlat (M.restrictSubtype M.E)) :
    (matroidGroundRankOneEquiv M F).1.1 = (Subtype.val : M.E → α) '' F.1.1 := rfl

theorem matroidGround_loops :
    (M.restrictSubtype M.E).loops = (Subtype.val : M.E → α) ⁻¹' M.loops := by
  change (M.restrictSubtype M.E).closure ∅ = (Subtype.val : M.E → α) ⁻¹' M.closure ∅
  rw [matroidGround_closure, Set.image_empty]

/-- The full original nonloop class is restored, not merely its cardinality. -/
theorem matroidGround_parallelClassSet (F : MatroidFlat (M.restrictSubtype M.E)) :
    (Subtype.val : M.E → α) '' (F.1 \ (M.restrictSubtype M.E).loops) =
      (matroidGroundFlatOrderIso M F).1 \ M.loops := by
  rw [matroidGround_loops, Set.image_sdiff Subtype.val_injective,
    matroidGround_image_preimage M M.loops M.loops_subset_ground]
  rfl

end BooleanAntichainsKernel
