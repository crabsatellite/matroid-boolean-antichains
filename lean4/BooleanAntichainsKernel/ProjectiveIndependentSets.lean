import BooleanAntichainsKernel.ProjectiveInternal

namespace BooleanAntichainsKernel

open Finset
open scoped Classical

/-- The paper's literal unordered independent projective-point set.
When k=dim(V), these are exactly its unordered projective bases. -/
abbrev ProjectiveIndependentSet (K V : Type*) [Field K] [AddCommGroup V] [Module K V] (k : ℕ) :=
  {B : Finset (Projectivization K V) // B.card = k ∧
    Projectivization.Independent (fun p : B ↦ p.1)}

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {k : ℕ}

noncomputable instance [Fintype V] : Fintype (ProjectiveIndependentSet K V k) :=
  Subtype.fintype _

theorem projectiveIndependent_reindex_iff {ι κ : Type*} (e : ι ≃ κ)
    (p : κ → Projectivization K V) :
    Projectivization.Independent (fun i ↦ p (e i)) ↔ Projectivization.Independent p := by
  simp only [Projectivization.independent_iff_iSupIndep]
  exact ⟨fun h ↦ h.comp' (t := fun j ↦ (p j).submodule) (f := e) e.surjective,
    fun h ↦ h.comp (f := e) e.injective⟩

def orderProjectiveFamily (B : ProjectiveIndependentSet K V k) (e : Fin k ≃ B.1) :
    OrderedProjectiveFrame K V k :=
  ⟨fun i ↦ (e i).1, (projectiveIndependent_reindex_iff e (fun p : B.1 ↦ p.1)).mpr B.2.2⟩

noncomputable def orderProjectiveSet (B : ProjectiveIndependentSet K V k) :
    OrderedProjectiveFrame K V k :=
  orderProjectiveFamily B (Finset.equivFinOfCardEq B.2.1).symm

theorem orderProjectiveSet_carrier (B : ProjectiveIndependentSet K V k) :
    orderedCarrier (orderProjectiveSet B).1 = B.1 :=
  orderedCarrier_of_equiv B.1 (Finset.equivFinOfCardEq B.2.1).symm

noncomputable def forgetOrderedProjective (p : OrderedProjectiveFrame K V k) :
    ProjectiveIndependentSet K V k := by
  let A := orderedCarrier p.1
  let e : Fin k ≃ A := indexEquivCarrier p.1 (orderedProjectiveFrame_injective p)
  have hc : A.card = k := by
    simp only [A, orderedCarrier, Finset.card_image_of_injective _ (orderedProjectiveFrame_injective p),
      card_univ, Fintype.card_fin]
  exact ⟨A, hc, (projectiveIndependent_reindex_iff e (fun q : A ↦ q.1)).mp p.2⟩

theorem forgetOrderedProjective_val (p : OrderedProjectiveFrame K V k) :
    (forgetOrderedProjective p).1 = orderedCarrier p.1 := rfl

theorem projectiveFrame_lines_carrier (p : OrderedProjectiveFrame K V k) :
    (orderedCarrier p.1).image Projectivization.submodule =
      orderedCarrier (fun i ↦ (p.1 i).submodule) := by
  simp only [orderedCarrier, Finset.image_image, Function.comp_def]

variable [FiniteDimensional K V]

noncomputable def projectiveSetToInternal (hk : k = Module.finrank K V)
    (B : ProjectiveIndependentSet K V k) : UnorderedInternalDecomposition K V k :=
  forgetOrderedInternal (projectiveFrameToInternal hk (orderProjectiveSet B))

theorem projectiveSetToInternal_val (hk : k = Module.finrank K V)
    (B : ProjectiveIndependentSet K V k) :
    (projectiveSetToInternal hk B).1 = B.1.image Projectivization.submodule := by
  change orderedCarrier (fun i ↦ ((orderProjectiveSet B).1 i).submodule) = _
  rw [← projectiveFrame_lines_carrier, orderProjectiveSet_carrier]

theorem projectiveSetToInternal_injective (hk : k = Module.finrank K V) :
    Function.Injective (projectiveSetToInternal (K := K) (V := V) hk) := by
  intro B C h
  apply Subtype.ext
  apply Finset.image_injective Projectivization.submodule_injective
  rw [← projectiveSetToInternal_val hk B, ← projectiveSetToInternal_val hk C, h]

theorem projectiveSetToInternal_surjective (hk : k = Module.finrank K V) :
    Function.Surjective (projectiveSetToInternal (K := K) (V := V) hk) := by
  intro D
  let p := internalToProjectiveFrame hk (orderUnorderedInternal D)
  refine ⟨forgetOrderedProjective p, Subtype.ext ?_⟩
  rw [projectiveSetToInternal_val, forgetOrderedProjective_val, projectiveFrame_lines_carrier]
  have hp : (fun i ↦ (p.1 i).submodule) = (orderUnorderedInternal D).1 :=
    funext (internalToProjectiveFrame_submodule hk (orderUnorderedInternal D))
  rw [hp]
  exact orderInternalFamily_carrier D (canonicalInternalEnumeration D)

/-- Actual unordered projective bases and actual unordered decompositions
into lines are bijective; both retain the same one-dimensional subspaces. -/
noncomputable def projectiveBasisEquivInternal (hk : k = Module.finrank K V) :
    ProjectiveIndependentSet K V k ≃ UnorderedInternalDecomposition K V k :=
  Equiv.ofBijective (projectiveSetToInternal hk)
    ⟨projectiveSetToInternal_injective hk, projectiveSetToInternal_surjective hk⟩

theorem projectiveBasisEquivInternal_lines (hk : k = Module.finrank K V)
    (B : ProjectiveIndependentSet K V k) :
    (projectiveBasisEquivInternal hk B).1 = B.1.image Projectivization.submodule :=
  projectiveSetToInternal_val hk B

theorem projectiveBasisEquivInternal_symm_lines (hk : k = Module.finrank K V)
    (D : UnorderedInternalDecomposition K V k) :
    ((projectiveBasisEquivInternal hk).symm D).1.image Projectivization.submodule = D.1 := by
  rw [← projectiveBasisEquivInternal_lines hk, Equiv.apply_symm_apply]

end BooleanAntichainsKernel
