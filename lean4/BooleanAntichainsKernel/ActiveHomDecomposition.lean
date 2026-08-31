import BooleanAntichainsKernel.ActiveAtoms

namespace BooleanAntichainsKernel

open Finset
open scoped Classical

variable {ι L : Type*} [DecidableEq ι] [Lattice L] [OrderTop L]

def liftAtomSet (A : Finset ι) (S : Finset A) : Finset ι := S.image Subtype.val

def pullAtomSet (A S : Finset ι) : Finset A := Finset.univ.filter fun a ↦ a.1 ∈ S

lemma liftAtomSet_subset (A : Finset ι) (S : Finset A) : liftAtomSet A S ⊆ A := by
  rintro i hi
  rcases Finset.mem_image.mp hi with ⟨a, _, rfl⟩
  exact a.2

lemma liftAtomSet_univ (A : Finset ι) : liftAtomSet A Finset.univ = A := by
  ext i
  constructor
  · intro hi
    exact liftAtomSet_subset A Finset.univ hi
  · intro hi
    exact Finset.mem_image.mpr ⟨⟨i, hi⟩, mem_univ _, rfl⟩

lemma liftAtomSet_union (A : Finset ι) (S T : Finset A) :
    liftAtomSet A (S ∪ T) = liftAtomSet A S ∪ liftAtomSet A T := Finset.image_union S T

lemma liftAtomSet_inter (A : Finset ι) (S T : Finset A) :
    liftAtomSet A (S ∩ T) = liftAtomSet A S ∩ liftAtomSet A T :=
  Finset.image_inter S T Subtype.val_injective

@[simp] lemma pullAtomSet_empty (A : Finset ι) : pullAtomSet A ∅ = ∅ := by ext a; simp [pullAtomSet]
@[simp] lemma pullAtomSet_univ [Fintype ι] (A : Finset ι) : pullAtomSet A Finset.univ = Finset.univ := by
  ext a
  simp [pullAtomSet]

lemma pullAtomSet_union (A S T : Finset ι) :
    pullAtomSet A (S ∪ T) = pullAtomSet A S ∪ pullAtomSet A T := by ext a; simp [pullAtomSet]

lemma pullAtomSet_inter (A S T : Finset ι) :
    pullAtomSet A (S ∩ T) = pullAtomSet A S ∩ pullAtomSet A T := by ext a; simp [pullAtomSet]

lemma lift_pullAtomSet (A S : Finset ι) : liftAtomSet A (pullAtomSet A S) = S ∩ A := by
  ext i
  constructor
  · intro hi
    rcases Finset.mem_image.mp hi with ⟨a, ha, rfl⟩
    exact Finset.mem_inter.mpr ⟨(Finset.mem_filter.mp ha).2, a.2⟩
  · intro hi
    rcases Finset.mem_inter.mp hi with ⟨hiS, hiA⟩
    exact Finset.mem_image.mpr ⟨⟨i, hiA⟩, Finset.mem_filter.mpr ⟨mem_univ _, hiS⟩, rfl⟩

lemma pull_liftAtomSet (A : Finset ι) (S : Finset A) : pullAtomSet A (liftAtomSet A S) = S := by
  ext a
  simp only [pullAtomSet, liftAtomSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · rintro ⟨b, hb, hba⟩
    exact (Subtype.ext hba : b = a) ▸ hb
  · intro ha
    exact ⟨a, ha, rfl⟩

lemma pullAtomSet_singleton_of_notMem (A : Finset ι) {i : ι} (hi : i ∉ A) :
    pullAtomSet A {i} = ∅ := by
  ext a
  simp only [pullAtomSet, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_singleton, Finset.notMem_empty, iff_false]
  intro ha
  exact hi (ha ▸ a.2)

variable [Fintype ι]

/-- Restrict the actual homomorphism to its uncollapsed atoms. -/
noncomputable def restrictTopHomToActive (f : TopBooleanHom ι L) :
    TopBooleanEmbedding (activeAtoms f) L := by
  refine ⟨⟨fun S ↦ f.1 (liftAtomSet (activeAtoms f) S), ?_, ?_, ?_⟩, ?_⟩
  · intro S T
    dsimp only
    rw [liftAtomSet_union, f.2.1]
  · intro S T
    dsimp only
    rw [liftAtomSet_inter, f.2.2.1]
  · dsimp only
    rw [liftAtomSet_univ, topHom_active_top]
  · intro S T hST
    apply Finset.image_injective Subtype.val_injective
    exact topHom_injective_on_active f (liftAtomSet_subset _ _) (liftAtomSet_subset _ _) hST

/-- Extend by intersecting the input with the given active set, exactly as
in the paper. `pullAtomSet` is the typed version of that intersection. -/
def extendActiveEmbedding (A : Finset ι) (g : TopBooleanEmbedding A L) : TopBooleanHom ι L :=
  ⟨fun S ↦ g.1.1 (pullAtomSet A S), by
    refine ⟨?_, ?_, ?_⟩
    · intro S T
      dsimp only
      rw [pullAtomSet_union, g.1.2.1]
    · intro S T
      dsimp only
      rw [pullAtomSet_inter, g.1.2.2.1]
    · dsimp only
      rw [pullAtomSet_univ, g.1.2.2.2]⟩

theorem activeAtoms_extend (A : Finset ι) (g : TopBooleanEmbedding A L) :
    activeAtoms (extendActiveEmbedding A g) = A := by
  ext i
  rw [mem_activeAtoms]
  change g.1.1 (pullAtomSet A {i}) ≠ g.1.1 (pullAtomSet A ∅) ↔ i ∈ A
  rw [pullAtomSet_empty]
  constructor
  · intro h
    by_contra hi
    exact h (congrArg g.1.1 (pullAtomSet_singleton_of_notMem A hi))
  · intro hi h
    have hs := g.2 h
    have hm : (⟨i, hi⟩ : A) ∈ pullAtomSet A {i} := by simp [pullAtomSet]
    rw [hs] at hm
    exact Finset.notMem_empty _ hm

theorem extend_restrictTopHom (f : TopBooleanHom ι L) :
    extendActiveEmbedding (activeAtoms f) (restrictTopHomToActive f) = f := by
  apply Subtype.ext
  funext S
  change f.1 (liftAtomSet (activeAtoms f) (pullAtomSet (activeAtoms f) S)) = f.1 S
  rw [lift_pullAtomSet]
  exact (topHom_eq_active_inter f S).symm

abbrev ActiveHomData (ι : Type*) [Fintype ι] [DecidableEq ι]
    (L : Type*) [Lattice L] [OrderTop L] := Σ A : Finset ι, TopBooleanEmbedding A L

def assembleActiveHom (x : ActiveHomData ι L) : TopBooleanHom ι L := extendActiveEmbedding x.1 x.2

theorem assembleActiveHom_injective : Function.Injective (assembleActiveHom (ι := ι) (L := L)) := by
  rintro ⟨A, g⟩ ⟨B, h⟩ heq
  have hAB : A = B := by
    have ha := congrArg activeAtoms heq
    simpa only [assembleActiveHom, activeAtoms_extend] using ha
  cases hAB
  apply congrArg (Sigma.mk A)
  apply Subtype.ext
  apply Subtype.ext
  funext S
  have hv := congrArg (fun f : TopBooleanHom ι L ↦ f.1 (liftAtomSet A S)) heq
  change g.1.1 (pullAtomSet A (liftAtomSet A S)) = h.1.1 (pullAtomSet A (liftAtomSet A S)) at hv
  simpa only [pull_liftAtomSet] using hv

/-- The paper's active-set decomposition, with its literal inverse. -/
noncomputable def activeHomDecompositionEquiv : ActiveHomData ι L ≃ TopBooleanHom ι L where
  toFun := assembleActiveHom
  invFun f := ⟨activeAtoms f, restrictTopHomToActive f⟩
  left_inv x := assembleActiveHom_injective (extend_restrictTopHom (assembleActiveHom x))
  right_inv := extend_restrictTopHom

@[simp] theorem activeHomDecompositionEquiv_symm_index (f : TopBooleanHom ι L) :
    (activeHomDecompositionEquiv.symm f).1 = activeAtoms f := rfl

end BooleanAntichainsKernel
