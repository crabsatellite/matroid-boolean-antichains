import BooleanAntichainsKernel.TopBooleanHom

/-! Active (uncollapsed) Boolean atoms and the literal kernel of a
top-preserving lattice homomorphism, following the proof of `thm:product`. -/

namespace BooleanAntichainsKernel

open Finset
open scoped Classical

variable {ι L : Type*} [Fintype ι] [DecidableEq ι] [Lattice L] [OrderTop L]

noncomputable def activeAtoms (f : TopBooleanHom ι L) : Finset ι :=
  Finset.univ.filter fun i ↦ f.1 {i} ≠ f.1 ∅

@[simp] lemma mem_activeAtoms (f : TopBooleanHom ι L) (i : ι) :
    i ∈ activeAtoms f ↔ f.1 {i} ≠ f.1 ∅ := by simp [activeAtoms]

lemma topBooleanHom_insert (f : TopBooleanHom ι L) (i : ι) (S : Finset ι) :
    f.1 (insert i S) = f.1 {i} ⊔ f.1 S := by
  simpa using f.2.1 {i} S

/-- Collapsed atoms do not change joins. -/
theorem topHom_eq_active_inter (f : TopBooleanHom ι L) (S : Finset ι) :
    f.1 S = f.1 (S ∩ activeAtoms f) := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    by_cases hactive : i ∈ activeAtoms f
    · rw [Finset.insert_inter_of_mem hactive, topBooleanHom_insert,
        topBooleanHom_insert, ih]
    · have hcollapse : f.1 {i} = f.1 ∅ := by
        by_contra hne
        exact hactive ((mem_activeAtoms f i).mpr hne)
      rw [Finset.insert_inter_of_notMem hactive, topBooleanHom_insert, hcollapse,
        sup_eq_right.mpr (topBooleanHom_mono f (Finset.empty_subset S)), ih]

lemma topHom_active_top (f : TopBooleanHom ι L) : f.1 (activeAtoms f) = ⊤ := by
  have h := topHom_eq_active_inter f Finset.univ
  simpa only [Finset.univ_inter, f.2.2.2] using h.symm

/-- Distinct subsets of active atoms cannot have the same image. -/
theorem topHom_injective_on_active (f : TopBooleanHom ι L)
    {S T : Finset ι} (hS : S ⊆ activeAtoms f) (hT : T ⊆ activeAtoms f)
    (hST : f.1 S = f.1 T) : S = T := by
  have hsub : ∀ {U V : Finset ι}, U ⊆ activeAtoms f → f.1 U = f.1 V → U ⊆ V := by
    intro U V hU huv i hiU
    by_contra hiV
    have hle : f.1 {i} ≤ f.1 V :=
      (topBooleanHom_mono f (Finset.singleton_subset_iff.mpr hiU)).trans_eq huv
    have hm := f.2.2.1 {i} V
    rw [Finset.singleton_inter_of_notMem hiV, inf_eq_left.mpr hle] at hm
    exact (mem_activeAtoms f i).mp (hU hiU) hm.symm
  exact Finset.Subset.antisymm (hsub hS hST) (hsub hT hST.symm)

theorem topHom_injective_iff_active_univ (f : TopBooleanHom ι L) :
    Function.Injective f.1 ↔ activeAtoms f = Finset.univ := by
  constructor
  · intro hinj
    ext i
    simp only [mem_activeAtoms, Finset.mem_univ, iff_true]
    intro hi
    have hs := hinj hi
    simp at hs
  · intro hactive S T hST
    apply topHom_injective_on_active f _ _ hST
    · rw [hactive]
      exact Finset.subset_univ S
    · rw [hactive]
      exact Finset.subset_univ T

variable {K : Type*} [Lattice K] [OrderTop K]

def prodTopBooleanHom (f : TopBooleanHom ι L) (g : TopBooleanHom ι K) :
    TopBooleanHom ι (L × K) :=
  ⟨fun S ↦ (f.1 S, g.1 S), by
    refine ⟨?_, ?_, ?_⟩
    · intro S T
      exact Prod.ext (f.2.1 S T) (g.2.1 S T)
    · intro S T
      exact Prod.ext (f.2.2.1 S T) (g.2.2.1 S T)
    · exact Prod.ext f.2.2.2 g.2.2.2⟩

lemma activeAtoms_prod (f : TopBooleanHom ι L) (g : TopBooleanHom ι K) :
    activeAtoms (prodTopBooleanHom f g) = activeAtoms f ∪ activeAtoms g := by
  ext i
  simp only [mem_activeAtoms, Finset.mem_union, prodTopBooleanHom,
    ne_eq, Prod.mk.injEq, not_and_or]

/-- The product map is injective exactly when the active sets cover every
label, including the zero-label case. -/
theorem prodTopBooleanHom_injective_iff (f : TopBooleanHom ι L) (g : TopBooleanHom ι K) :
    Function.Injective (prodTopBooleanHom f g).1 ↔ activeAtoms f ∪ activeAtoms g = Finset.univ := by
  rw [topHom_injective_iff_active_univ, activeAtoms_prod]

end BooleanAntichainsKernel
