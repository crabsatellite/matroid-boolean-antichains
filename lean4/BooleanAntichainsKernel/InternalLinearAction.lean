import BooleanAntichainsKernel.SubspaceDimensions

namespace BooleanAntichainsKernel

open scoped Classical

variable {R V W Z : Type*} [Ring R]
variable [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
variable [AddCommGroup Z] [Module R Z] {k : ℕ}

/-- Send each actual summand to its linear image under the given isomorphism. -/
def mapInternalDecomposition (g : V ≃ₗ[R] W) (D : OrderedInternalDecomposition R V k) :
    OrderedInternalDecomposition R W k := by
  let e := Submodule.orderIsoMapComap g
  refine ⟨fun i ↦ e (D.1 i), ?_, ?_⟩
  · apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    · exact D.2.1.submodule_iSupIndep.map_orderIso e
    · rw [← e.map_iSup, D.2.1.submodule_iSup_eq_top, e.map_top]
  · intro i h
    exact D.2.2 i (e.injective (h.trans e.map_bot.symm))

@[simp] theorem mapInternalDecomposition_apply (g : V ≃ₗ[R] W)
    (D : OrderedInternalDecomposition R V k) (i : Fin k) :
    (mapInternalDecomposition g D).1 i = (D.1 i).map (g : V →ₗ[R] W) := rfl

theorem mapInternalDecomposition_refl (D : OrderedInternalDecomposition R V k) :
    mapInternalDecomposition (LinearEquiv.refl R V) D = D := by
  apply Subtype.ext
  funext i
  change (D.1 i).map (LinearMap.id : V →ₗ[R] V) = D.1 i
  exact Submodule.map_id (p := D.1 i)

theorem mapInternalDecomposition_trans (g : V ≃ₗ[R] W) (h : W ≃ₗ[R] Z)
    (D : OrderedInternalDecomposition R V k) :
    mapInternalDecomposition (g.trans h) D =
      mapInternalDecomposition h (mapInternalDecomposition g D) := by
  apply Subtype.ext
  funext i
  exact Submodule.map_comp (g : V →ₗ[R] W) (h : W →ₗ[R] Z) (D.1 i)

instance orderedInternalMulAction : MulAction (V ≃ₗ[R] V) (OrderedInternalDecomposition R V k) where
  smul := mapInternalDecomposition
  one_smul := mapInternalDecomposition_refl
  mul_smul g h D := mapInternalDecomposition_trans h g D

@[simp] theorem orderedInternal_smul_apply (g : V ≃ₗ[R] V)
    (D : OrderedInternalDecomposition R V k) (i : Fin k) :
    (g • D).1 i = (D.1 i).map (g : V →ₗ[R] V) := rfl

theorem mapInternalDecomposition_finrank (g : V ≃ₗ[R] W)
    (D : OrderedInternalDecomposition R V k) (i : Fin k) :
    Module.finrank R ((mapInternalDecomposition g D).1 i) = Module.finrank R (D.1 i) :=
  (g.submoduleMap (D.1 i)).finrank_eq.symm

/-- Ordered internal decompositions with a specified actual dimension profile. -/
abbrev SizedInternalDecomposition (R V : Type*) [Ring R] [AddCommGroup V] [Module R V]
    {k : ℕ} (p : Fin k → ℕ) :=
  {D : OrderedInternalDecomposition R V k // ∀ i, Module.finrank R (D.1 i) = p i}

noncomputable instance [Fintype V] (p : Fin k → ℕ) : Fintype (SizedInternalDecomposition R V p) :=
  Subtype.fintype _

def mapSizedInternal (g : V ≃ₗ[R] W) {p : Fin k → ℕ} (D : SizedInternalDecomposition R V p) :
    SizedInternalDecomposition R W p :=
  ⟨mapInternalDecomposition g D.1, fun i ↦ (mapInternalDecomposition_finrank g D.1 i).trans (D.2 i)⟩

instance sizedInternalMulAction (p : Fin k → ℕ) : MulAction (V ≃ₗ[R] V) (SizedInternalDecomposition R V p) where
  smul g D := mapSizedInternal (V := V) (W := V) g D
  one_smul D := by
    apply Subtype.ext
    change mapInternalDecomposition (LinearEquiv.refl R V) D.1 = D.1
    exact mapInternalDecomposition_refl D.1
  mul_smul g h D := by
    apply Subtype.ext
    exact mapInternalDecomposition_trans h g D.1

@[simp] theorem sizedInternal_smul_apply {p : Fin k → ℕ} (g : V ≃ₗ[R] V)
    (D : SizedInternalDecomposition R V p) (i : Fin k) :
    (g • D).1.1 i = (D.1.1 i).map (g : V →ₗ[R] V) := rfl

end BooleanAntichainsKernel
