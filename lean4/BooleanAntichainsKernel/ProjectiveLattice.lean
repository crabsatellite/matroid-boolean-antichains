import BooleanAntichainsKernel.LatticeTransport
import BooleanAntichainsKernel.SubspaceTopProduct
import Mathlib.LinearAlgebra.Projectivization.Subspace
import Mathlib.LinearAlgebra.Projectivization.Independence

namespace BooleanAntichainsKernel

open Finset
open scoped Classical

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

noncomputable instance [Fintype V] : Fintype (Projectivization K V) :=
  Fintype.ofInjective Projectivization.submodule Projectivization.submodule_injective

noncomputable instance [Fintype V] : Fintype (Projectivization.Subspace K V) :=
  Fintype.ofInjective Projectivization.Subspace.submodule
    Projectivization.Subspace.submodule.injective

/-- The lattice of actual projective subspaces (sets of projective points)
and the lattice of actual vector subspaces, including their bottom elements. -/
def projectiveSubspaceOrderIso : Projectivization.Subspace K V ≃o Submodule K V :=
  Projectivization.Subspace.submodule

theorem projectiveSubspaceOrderIso_mem (S : Projectivization.Subspace K V)
    (v : V) (hv : v ≠ 0) :
    v ∈ projectiveSubspaceOrderIso S ↔ Projectivization.mk K v hv ∈ S :=
  Projectivization.Subspace.mem_submodule_iff S hv

theorem projectiveSubspaceOrderIso_symm_mem (U : Submodule K V) (p : Projectivization K V) :
    p ∈ projectiveSubspaceOrderIso.symm U ↔ p.submodule ≤ U :=
  Submodule.mem_projectivization_iff_submodule_le U p

noncomputable def projectiveAntichainEquiv (k : ℕ) :
    BooleanAntichain k (Projectivization.Subspace K V) ≃ BooleanAntichain k (Submodule K V) :=
  booleanAntichainOrderIsoEquiv projectiveSubspaceOrderIso k

theorem projectiveAntichainEquiv_val (k : ℕ)
    (C : BooleanAntichain k (Projectivization.Subspace K V)) :
    (projectiveAntichainEquiv k C).1 = C.1.image Projectivization.Subspace.submodule := by
  change mapFamily projectiveSubspaceOrderIso C.1 = _
  rw [mapFamily, Equiv.finsetCongr_apply, Finset.map_eq_image]
  rfl

theorem projectiveAntichainEquiv_atoms (k : ℕ)
    (C : BooleanAntichain k (Projectivization.Subspace K V)) :
    antichainAtoms (projectiveAntichainEquiv k C).1 =
      mapFamily projectiveSubspaceOrderIso (antichainAtoms C.1) :=
  antichainAtoms_mapFamily projectiveSubspaceOrderIso C.1

end BooleanAntichainsKernel
