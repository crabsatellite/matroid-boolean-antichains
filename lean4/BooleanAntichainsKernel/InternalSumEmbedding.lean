import BooleanAntichainsKernel.SubspaceQuotientEmbedding
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Order.SupIndep

namespace BooleanAntichainsKernel

open Finset
open scoped Classical

lemma independent_finset_sup_inter {ι L : Type*} [Fintype ι] [DecidableEq ι]
    [Lattice L] [OrderBot L] [IsModularLattice L] (U : ι → L)
    (hU : Finset.univ.SupIndep U) (S T : Finset ι) :
    (S ∩ T).sup U = S.sup U ⊓ T.sup U := by
  have hle : (S ∩ T).sup U ≤ T.sup U := Finset.sup_mono Finset.inter_subset_right
  have hd : Disjoint ((S \ T).sup U) (T.sup U) :=
    hU.disjoint_sup_sup (Finset.subset_univ _) (Finset.subset_univ _) Finset.sdiff_disjoint
  have hpart : (S ∩ T).sup U ⊔ (S \ T).sup U = S.sup U := by
    rw [← Finset.sup_union, Finset.union_comm, Finset.sdiff_union_inter]
  rw [← hpart, sup_inf_assoc_of_le _ hle, hd.eq_bot, sup_bot_eq]

variable (R V : Type*) [Ring R] [AddCommGroup V] [Module R V]

/-- The actual internal direct sum, with nonzero summands as in the paper. -/
abbrev OrderedInternalDecomposition (k : ℕ) :=
  {U : Fin k → Submodule R V // DirectSum.IsInternal U ∧ ∀ i, U i ≠ ⊥}

noncomputable instance [Fintype V] (k : ℕ) : Fintype (OrderedInternalDecomposition R V k) :=
  Subtype.fintype _

variable {R V} {k : ℕ}

namespace OrderedInternalDecomposition

lemma supIndep (D : OrderedInternalDecomposition R V k) : Finset.univ.SupIndep D.1 :=
  D.2.1.submodule_iSupIndep.sup_indep_univ

lemma sup_univ (D : OrderedInternalDecomposition R V k) : Finset.univ.sup D.1 = ⊤ := by
  simpa [Finset.sup_eq_iSup] using D.2.1.submodule_iSup_eq_top

lemma sup_inter (D : OrderedInternalDecomposition R V k) (S T : Finset (Fin k)) :
    (S ∩ T).sup D.1 = S.sup D.1 ⊓ T.sup D.1 :=
  independent_finset_sup_inter D.1 D.supIndep S T

lemma sup_injective (D : OrderedInternalDecomposition R V k) :
    Function.Injective (fun S : Finset (Fin k) ↦ S.sup D.1) := by
  have hsub : ∀ {S T : Finset (Fin k)}, S.sup D.1 = T.sup D.1 → S ⊆ T := by
    intro S T h i hi
    apply (D.supIndep.le_sup_iff (Finset.subset_univ T) (Finset.mem_univ i) D.2.2).mp
    exact (Finset.le_sup hi).trans_eq h
  exact fun _ _ h ↦ Finset.Subset.antisymm (hsub h) (hsub h.symm)

/-- The Boolean faces are the actual submodule sums of subcollections. -/
def toBottomEmbedding (D : OrderedInternalDecomposition R V k) :
    BottomTopBooleanEmbedding (Fin k) (Submodule R V) :=
  ⟨⟨⟨fun S ↦ S.sup D.1,
    (fun _ _ ↦ Finset.sup_union), D.sup_inter, D.sup_univ⟩,
    D.sup_injective⟩, by simp⟩

@[simp] theorem toBottomEmbedding_face (D : OrderedInternalDecomposition R V k)
    (S : Finset (Fin k)) : D.toBottomEmbedding.1.1.1 S = S.sup D.1 := rfl

/-- This is the displayed inverse coatom construction in the quotient. -/
theorem toBottomEmbedding_coatom (D : OrderedInternalDecomposition R V k) (i : Fin k) :
    topHomCoatoms D.toBottomEmbedding.1.1 i = (Finset.univ.erase i).sup D.1 := rfl

end OrderedInternalDecomposition
end BooleanAntichainsKernel
