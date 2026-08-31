import BooleanAntichainsKernel.LinearAutomorphismCard
import Mathlib.Data.Fintype.BigOperators

namespace BooleanAntichainsKernel

open Finset
open scoped Classical

/-- An actual ordered independent d-tuple, retaining its vectors in V. -/
def IndependentFrame (K V : Type*) [Field K] [AddCommGroup V] [Module K V] (d : ℕ) :=
  {v : Fin d → V // LinearIndependent K v}

/-- The actual dimension-d subspace carrier, not a numerical surrogate. -/
def DimensionSubspace (K V : Type*) [Field K] [AddCommGroup V] [Module K V] (d : ℕ) :=
  {W : Submodule K V // Module.finrank K W = d}

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {d : ℕ}

noncomputable instance [Fintype V] : Fintype (IndependentFrame K V d) :=
  inferInstanceAs (Fintype {v : Fin d → V // LinearIndependent K v})

noncomputable instance [Fintype V] : Fintype (DimensionSubspace K V d) :=
  inferInstanceAs (Fintype {W : Submodule K V // Module.finrank K W = d})

/-- Forget only the containing subspace, by its actual inclusion into V. -/
def subspaceFrameForget (a : Σ W : DimensionSubspace K V d, IndependentFrame K W.1 d) :
    IndependentFrame K V d :=
  ⟨fun i ↦ (a.2.1 i : V), a.2.2.map' a.1.1.subtype a.1.1.ker_subtype⟩

variable [FiniteDimensional K V]

theorem subspaceFrameForget_span
    (a : Σ W : DimensionSubspace K V d, IndependentFrame K W.1 d) :
    Submodule.span K (Set.range (subspaceFrameForget a).1) = a.1.1 := by
  apply Submodule.eq_of_le_of_finrank_eq
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact (a.2.1 i).2
  · exact (finrank_span_eq_card (subspaceFrameForget a).2).trans
      ((Fintype.card_fin d).trans a.1.2.symm)

theorem subspaceFrameForget_injective : Function.Injective
    (subspaceFrameForget (K := K) (V := V) (d := d)) := by
  rintro ⟨W, v⟩ ⟨Z, w⟩ h
  have hW : W = Z := Subtype.ext <| (subspaceFrameForget_span ⟨W, v⟩).symm.trans
    ((congrArg (fun a : IndependentFrame K V d ↦ Submodule.span K (Set.range a.1)) h).trans
      (subspaceFrameForget_span ⟨Z, w⟩))
  subst Z
  have hvw : v = w := by
    apply Subtype.ext
    funext i
    apply Subtype.ext
    exact congrFun (congrArg (fun a : IndependentFrame K V d ↦ a.1) h) i
  subst w
  rfl

omit [FiniteDimensional K V] in
theorem subspaceFrameForget_surjective : Function.Surjective
    (subspaceFrameForget (K := K) (V := V) (d := d)) := by
  intro v
  let W : DimensionSubspace K V d :=
    ⟨Submodule.span K (Set.range v.1), by simpa using finrank_span_eq_card v.2⟩
  let w : IndependentFrame K W.1 d :=
    ⟨fun i ↦ ⟨v.1 i, Submodule.subset_span (Set.mem_range_self i)⟩,
      linearIndependent_span v.2⟩
  exact ⟨⟨W, w⟩, rfl⟩

/-- Each independent frame is counted once, in its unique actual span. -/
noncomputable def subspaceFrameSigmaEquiv :
    (Σ W : DimensionSubspace K V d, IndependentFrame K W.1 d) ≃ IndependentFrame K V d :=
  Equiv.ofBijective subspaceFrameForget
    ⟨subspaceFrameForget_injective, subspaceFrameForget_surjective⟩

theorem subspaceFrameSigmaEquiv_vectors
    (a : Σ W : DimensionSubspace K V d, IndependentFrame K W.1 d) (i : Fin d) :
    (subspaceFrameSigmaEquiv a).1 i = (a.2.1 i : V) := rfl

variable [Fintype K] [Fintype V]

omit [FiniteDimensional K V] in
theorem independentFrame_card (hd : d ≤ Module.finrank K V) :
    Fintype.card (IndependentFrame K V d) =
      ∏ i : Fin d, ((Fintype.card K) ^ Module.finrank K V - (Fintype.card K) ^ i.1) := by
  rw [← Nat.card_eq_fintype_card]
  exact card_linearIndependent hd

omit [FiniteDimensional K V] in
theorem subspaceFrame_card (W : DimensionSubspace K V d) :
    Fintype.card (IndependentFrame K W.1 d) = generalLinearCard K d := by
  rw [independentFrame_card W.2.ge, W.2, generalLinearCard_product]

theorem dimensionSubspace_card_mul (hd : d ≤ Module.finrank K V) :
    Fintype.card (DimensionSubspace K V d) * generalLinearCard K d =
      ∏ i : Fin d, ((Fintype.card K) ^ Module.finrank K V - (Fintype.card K) ^ i.1) := by
  rw [← independentFrame_card hd, ← Fintype.card_congr
    (subspaceFrameSigmaEquiv (K := K) (V := V) (d := d)), Fintype.card_sigma]
  simp only [subspaceFrame_card, sum_const, card_univ, smul_eq_mul]

end BooleanAntichainsKernel
