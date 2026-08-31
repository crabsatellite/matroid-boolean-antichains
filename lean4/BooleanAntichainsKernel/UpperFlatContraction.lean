import BooleanAntichainsKernel.RankTightFibers
import BooleanAntichainsKernel.AntichainBottomFibres

namespace BooleanAntichainsKernel

open scoped Classical Matroid

variable {α : Type*}

/-- Equality transport preserves the exact underlying flat set. -/
def matroidFlatEqualityOrderIso {M N : Matroid α} (h : M = N) : MatroidFlat M ≃o MatroidFlat N where
  toFun F := ⟨F.1, h ▸ F.2⟩
  invFun F := ⟨F.1, h.symm ▸ F.2⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl
  map_rel_iff' := Iff.rfl

theorem matroidFlatEqualityOrderIso_val {M N : Matroid α} (h : M = N) (F : MatroidFlat M) :
    (matroidFlatEqualityOrderIso h F).1 = F.1 := rfl

variable {M : Matroid α}

local instance (X : MatroidFlat M) : Fact (X ≤ (⊤ : MatroidFlat M)) := ⟨le_top⟩

/-- Consume the already proved interval minor and its exact equality to
the actual contraction. The map is literally F minus X. -/
noncomputable def upperFlatContractOrderIso (X : MatroidFlat M) :
    Set.Ici X ≃o MatroidFlat (M ／ X.1) :=
  (iccTopOrderIsoIci X).symm.trans
    ((flatIntervalMinorOrderIso X (⊤ : MatroidFlat M) le_top).trans
      (matroidFlatEqualityOrderIso (flatIntervalMinor_top_eq_contract X)))

theorem upperFlatContractOrderIso_val (X : MatroidFlat M) (F : Set.Ici X) :
    (upperFlatContractOrderIso X F).1 = F.1.1 \ X.1 := rfl

theorem upperFlatContractOrderIso_symm_val (X : MatroidFlat M) (F : MatroidFlat (M ／ X.1)) :
    ((upperFlatContractOrderIso X).symm F).1.1 = F.1 ∪ X.1 := rfl

variable [Fintype α]

theorem upperFlatContractOrderIso_rank_add (X : MatroidFlat M) (F : Set.Ici X) :
    MatroidFlat.rank (upperFlatContractOrderIso X F) + MatroidFlat.rank X = MatroidFlat.rank F.1 := by
  change matroidRank (M ／ X.1) (F.1.1 \ X.1) + matroidRank M X.1 = matroidRank M F.1.1
  have h := matroidRank_contract_add M X.2.subset_ground
    (S := F.1.1 \ X.1) (fun _ he ↦ ⟨F.1.2.subset_ground he.1, he.2⟩)
  rw [Set.sdiff_union_of_subset F.2] at h
  exact h

theorem upperFlatContractOrderIso_rank (X : MatroidFlat M) (F : Set.Ici X) :
    MatroidFlat.rank (upperFlatContractOrderIso X F) = MatroidFlat.rank F.1 - MatroidFlat.rank X :=
  Nat.eq_sub_of_add_eq (upperFlatContractOrderIso_rank_add X F)

end BooleanAntichainsKernel
