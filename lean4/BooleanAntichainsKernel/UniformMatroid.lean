import BooleanAntichainsKernel.MinorRank
import Mathlib.Combinatorics.Matroid.IndepAxioms

/-! The actual uniform matroid used by both uniform enumeration theorems.
Independence means containment in the ground set and cardinality at most r.
The finite matroid axioms are proved, not supplied as a reference premise. -/

namespace BooleanAntichainsKernel

open Set
open scoped Classical

variable {α : Type*} [Fintype α]

noncomputable def uniformOn (E : Set α) (r : ℕ) : Matroid α :=
  (IndepMatroid.ofFinite (Set.toFinite E) (fun I ↦ I ⊆ E ∧ I.ncard ≤ r)
    ⟨Set.empty_subset E, by simp⟩
    (fun {_I _J} hJ hIJ ↦ ⟨hIJ.trans hJ.1, (Set.ncard_le_ncard hIJ).trans hJ.2⟩)
    (by
      intro I J hI hJ hIJ
      have hnot : ¬ J ⊆ I := fun h ↦ hIJ.not_ge (Set.ncard_le_ncard h)
      obtain ⟨e, heJ, heI⟩ := Set.not_subset.mp hnot
      refine ⟨e, heJ, heI, Set.insert_subset_iff.mpr ⟨hJ.1 heJ, hI.1⟩, ?_⟩
      rw [Set.ncard_insert_of_notMem heI]
      omega)
    (fun {_I} hI ↦ hI.1)).matroid

@[simp] theorem uniformOn_ground (E : Set α) (r : ℕ) : (uniformOn E r).E = E := rfl

@[simp] theorem uniformOn_indep_iff (E : Set α) (r : ℕ) (I : Set α) :
    (uniformOn E r).Indep I ↔ I ⊆ E ∧ I.ncard ≤ r := Iff.rfl

/-- Bases are exactly the r-subsets when the stated rank is at most the
ground size. This is derived by the actual independent-set augmentation. -/
theorem uniformOn_isBase_iff (E : Set α) (r : ℕ) (hr : r ≤ E.ncard) (B : Set α) :
    (uniformOn E r).IsBase B ↔ B ⊆ E ∧ B.ncard = r := by
  constructor
  · intro hB
    have hind := (uniformOn_indep_iff E r B).mp hB.indep
    refine ⟨hind.1, Nat.le_antisymm hind.2 ?_⟩
    by_contra hlt
    have hBr : B.ncard < r := Nat.lt_of_not_ge hlt
    have hBE : B.ncard < E.ncard := hBr.trans_le hr
    have hnot : ¬ E ⊆ B := fun h ↦ hBE.not_ge (Set.ncard_le_ncard h)
    obtain ⟨e, heE, heB⟩ := Set.not_subset.mp hnot
    have hi : (uniformOn E r).Indep (insert e B) := by
      apply (uniformOn_indep_iff E r _).mpr
      refine ⟨Set.insert_subset_iff.mpr ⟨heE, hind.1⟩, ?_⟩
      rw [Set.ncard_insert_of_notMem heB]
      omega
    have heq := hB.eq_of_subset_indep hi (Set.subset_insert e B)
    exact heB (heq.symm ▸ Set.mem_insert e B)
  · rintro ⟨hBE, hcard⟩
    have hi : (uniformOn E r).Indep B := (uniformOn_indep_iff E r B).mpr ⟨hBE, hcard.le⟩
    apply hi.isBase_of_maximal
    intro J hJ hBJ
    apply Set.eq_of_subset_of_ncard_le hBJ
    rw [hcard]
    exact ((uniformOn_indep_iff E r J).mp hJ).2

theorem uniformOn_ground_rank (E : Set α) (r : ℕ) (hr : r ≤ E.ncard) :
    matroidRank (uniformOn E r) E = r := by
  obtain ⟨B, hB⟩ := (uniformOn E r).exists_isBase
  calc
    _ = B.ncard := matroidRank_isBasis hB.isBasis_ground
    _ = r := ((uniformOn_isBase_iff E r hr B).mp hB).2

end BooleanAntichainsKernel
