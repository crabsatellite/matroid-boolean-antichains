import BooleanAntichainsKernel.ProjectiveFrames
import BooleanAntichainsKernel.UnorderedInternalBijection

namespace BooleanAntichainsKernel

open Finset
open scoped Classical

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable [FiniteDimensional K V] {k : ℕ}

theorem internal_summand_finrank_one (hk : k = Module.finrank K V)
    (D : OrderedInternalDecomposition K V k) (i : Fin k) : Module.finrank K (D.1 i) = 1 := by
  let p : PositiveDimensionProfile k k :=
    ⟨fun j ↦ Module.finrank K (D.1 j), D.summand_finrank_ge_one,
      D.finrank_eq_sum.symm.trans hk.symm⟩
  exact positiveDimensionProfile_diagonal p i

/-- A full-length independent projective frame spans V, and its actual
one-dimensional subspaces form the canonical internal direct sum. -/
noncomputable def projectiveFrameToInternal (hk : k = Module.finrank K V)
    (p : OrderedProjectiveFrame K V k) : OrderedInternalDecomposition K V k := by
  refine ⟨fun i ↦ (p.1 i).submodule, ?_, ?_⟩
  · apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    · exact Projectivization.independent_iff_iSupIndep.mp p.2
    · simp_rw [Projectivization.submodule_eq]
      rw [← Submodule.span_range_eq_iSup]
      exact (Projectivization.independent_iff.mp p.2).span_eq_top_of_card_eq_finrank'
        ((Fintype.card_fin k).trans hk)
  · intro i
    exact Submodule.one_le_finrank_iff.mp (p.1 i).finrank_submodule.symm.le

noncomputable def internalToProjectiveFrame (hk : k = Module.finrank K V)
    (D : OrderedInternalDecomposition K V k) : OrderedProjectiveFrame K V k :=
  ⟨fun i ↦ Projectivization.mk'' (D.1 i) (internal_summand_finrank_one hk D i),
    Projectivization.independent_iff_iSupIndep.mpr (by
      simpa only [Projectivization.submodule_mk''] using D.2.1.submodule_iSupIndep)⟩

theorem internalToProjectiveFrame_submodule (hk : k = Module.finrank K V)
    (D : OrderedInternalDecomposition K V k) (i : Fin k) :
    ((internalToProjectiveFrame hk D).1 i).submodule = D.1 i :=
  Projectivization.submodule_mk'' _ _

noncomputable def orderedProjectiveEquivInternal (hk : k = Module.finrank K V) :
    OrderedProjectiveFrame K V k ≃ OrderedInternalDecomposition K V k where
  toFun := projectiveFrameToInternal hk
  invFun := internalToProjectiveFrame hk
  left_inv p := by
    apply Subtype.ext
    funext i
    apply Projectivization.submodule_injective
    exact internalToProjectiveFrame_submodule hk (projectiveFrameToInternal hk p) i
  right_inv D := by
    apply Subtype.ext
    funext i
    exact internalToProjectiveFrame_submodule hk D i

theorem orderedProjectiveEquivInternal_apply (hk : k = Module.finrank K V)
    (p : OrderedProjectiveFrame K V k) (i : Fin k) :
    (orderedProjectiveEquivInternal hk p).1 i = (p.1 i).submodule := rfl

variable [Fintype V]

/-- Full size forces the literal common intersection to be zero, by the
proved quotient dimension bound and rank-nullity. -/
theorem maximalSubspaceAntichain_bottom (hk : k = Module.finrank K V)
    (C : BooleanAntichain k (Submodule K V)) : C.1.inf id = ⊥ := by
  have hq : k ≤ Module.finrank K (V ⧸ C.1.inf id) :=
    (orderUnorderedInternal ((subspaceUnorderedSigmaEquiv k).symm C).2).size_le_finrank
  have hdim := Submodule.finrank_quotient_add_finrank (R := K) (C.1.inf id)
  apply Submodule.finrank_eq_zero.mp
  omega

noncomputable def maximalSubspaceAntichainEquivBottom (hk : k = Module.finrank K V) :
    BooleanAntichain k (Submodule K V) ≃ BottomBooleanAntichain k (Submodule K V) where
  toFun C := ⟨C, maximalSubspaceAntichain_bottom hk C⟩
  invFun C := C.1
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def maximalSubspaceAntichainEquivInternal (hk : k = Module.finrank K V) :
    BooleanAntichain k (Submodule K V) ≃ UnorderedInternalDecomposition K V k :=
  (maximalSubspaceAntichainEquivBottom hk).trans bottomAntichainEquivUnorderedInternal

theorem maximalSubspaceAntichainEquivInternal_atoms (hk : k = Module.finrank K V)
    (C : BooleanAntichain k (Submodule K V)) :
    (maximalSubspaceAntichainEquivInternal hk C).1 = antichainAtoms C.1 :=
  bottomAntichainToUnorderedInternal_val _

theorem maximalSubspaceAntichainEquivInternal_coatoms (hk : k = Module.finrank K V)
    (D : UnorderedInternalDecomposition K V k) :
    ((maximalSubspaceAntichainEquivInternal hk).symm D).1 = basisCoatoms D.1 :=
  unorderedInternalToBottomAntichain_val D

end BooleanAntichainsKernel
