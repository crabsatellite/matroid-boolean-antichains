import BooleanAntichainsKernel.Core
import Mathlib.Data.Fintype.Powerset
import Mathlib.Combinatorics.Matroid.Rank.ENat

/-!
# The finite lattice of flats of a mathlib matroid

The carrier is the literal subtype of `Matroid.IsFlat`; meet is intersection,
join is matroid closure of union, bottom is the loop flat, and top is the
ground set.
-/

namespace BooleanAntichainsKernel

open Set

abbrev MatroidFlat {α : Type*} (M : Matroid α) := {F : Set α // M.IsFlat F}

namespace MatroidFlat

variable {α : Type*} {M : Matroid α}

instance : SetLike (MatroidFlat M) α where
  coe F := F.1
  coe_injective := Subtype.val_injective

instance : PartialOrder (MatroidFlat M) :=
  PartialOrder.lift (fun F ↦ F.1) Subtype.val_injective

private lemma isFlat_inter (F G : MatroidFlat M) : M.IsFlat (F.1 ∩ G.1) := by
  have hflat : M.IsFlat (⋂ b : Bool, cond b F.1 G.1) :=
    Matroid.IsFlat.iInter fun b ↦ by cases b <;> simp [F.2, G.2]
  convert hflat using 1
  ext x
  simp [and_comm]

instance : Lattice (MatroidFlat M) where
  sup F G := ⟨M.closure (F.1 ∪ G.1), M.isFlat_closure _⟩
  le_sup_left F G := by
    change F.1 ⊆ M.closure (F.1 ∪ G.1)
    exact (M.subset_closure_of_subset (subset_union_left)
      (union_subset F.2.subset_ground G.2.subset_ground))
  le_sup_right F G := by
    change G.1 ⊆ M.closure (F.1 ∪ G.1)
    exact (M.subset_closure_of_subset (subset_union_right)
      (union_subset F.2.subset_ground G.2.subset_ground))
  sup_le F G H hF hG := by
    change M.closure (F.1 ∪ G.1) ⊆ H.1
    rw [← H.2.closure]
    exact M.closure_subset_closure (union_subset hF hG)
  inf F G := ⟨F.1 ∩ G.1, isFlat_inter F G⟩
  inf_le_left F G := inter_subset_left
  inf_le_right F G := inter_subset_right
  le_inf F G H hF hG := subset_inter hF hG

instance : OrderTop (MatroidFlat M) where
  top := ⟨M.E, M.ground_isFlat⟩
  le_top F := F.2.subset_ground

instance : OrderBot (MatroidFlat M) where
  bot := ⟨M.closure ∅, M.isFlat_closure _⟩
  bot_le F := by
    change M.closure ∅ ⊆ F.1
    rw [← F.2.closure]
    exact M.closure_subset_closure (empty_subset _)

@[simp] theorem coe_top : ((⊤ : MatroidFlat M) : Set α) = M.E := rfl

@[simp] theorem coe_bot : ((⊥ : MatroidFlat M) : Set α) = M.closure ∅ := rfl

@[simp] theorem coe_inf (F G : MatroidFlat M) :
    ((F ⊓ G : MatroidFlat M) : Set α) = F.1 ∩ G.1 := rfl

@[simp] theorem coe_sup (F G : MatroidFlat M) :
    ((F ⊔ G : MatroidFlat M) : Set α) = M.closure (F.1 ∪ G.1) := rfl

@[simp] theorem val_top : (⊤ : MatroidFlat M).1 = M.E := rfl

@[simp] theorem val_bot : (⊥ : MatroidFlat M).1 = M.closure ∅ := rfl

@[simp] theorem val_inf (F G : MatroidFlat M) : (F ⊓ G).1 = F.1 ∩ G.1 := rfl

@[simp] theorem val_sup (F G : MatroidFlat M) :
    (F ⊔ G).1 = M.closure (F.1 ∪ G.1) := rfl

noncomputable instance [Fintype α] : DecidableEq (MatroidFlat M) := Classical.decEq _

noncomputable instance [Fintype α] : Fintype (MatroidFlat M) :=
  Fintype.ofInjective (fun F : MatroidFlat M ↦ F.1) Subtype.val_injective

end MatroidFlat

end BooleanAntichainsKernel
