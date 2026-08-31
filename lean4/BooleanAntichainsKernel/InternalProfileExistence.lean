import BooleanAntichainsKernel.InternalProfileTransitivity
import Mathlib.LinearAlgebra.DirectSum.Finite

namespace BooleanAntichainsKernel

open scoped Classical DirectSum

abbrev CoordinateSum (K : Type*) [Field K] {k : ℕ} (p : Fin k → ℕ) :=
  ⨁ i : Fin k, (Fin (p i) → K)

variable {K : Type*} [Field K] {k : ℕ}

def coordinateComponent (p : Fin k → ℕ) (i : Fin k) : Submodule K (CoordinateSum K p) :=
  LinearMap.range (DirectSum.lof K (Fin k) (fun j ↦ Fin (p j) → K) i)

theorem coordinateComponents_iSup (p : Fin k → ℕ) :
    (⨆ i, coordinateComponent (K := K) p i) = ⊤ :=
  DFinsupp.iSup_range_lsingle

theorem coordinateComponents_iSupIndep (p : Fin k → ℕ) :
    iSupIndep (coordinateComponent (K := K) p) := by
  intro i
  have hrest : (⨆ j, ⨆ (_ : j ≠ i), coordinateComponent (K := K) p j) ≤
      LinearMap.ker (DFinsupp.lapply i : CoordinateSum K p →ₗ[K] (Fin (p i) → K)) := by
    refine iSup_le fun j ↦ iSup_le fun hji ↦ ?_
    intro x hx
    rcases hx with ⟨v, rfl⟩
    change (DFinsupp.single (β := fun j : Fin k ↦ Fin (p j) → K) j v) i = 0
    exact DFinsupp.single_eq_of_ne hji.symm
  apply Submodule.disjoint_def.mpr
  intro x hxi hxrest
  rcases hxi with ⟨v, rfl⟩
  have hz := hrest hxrest
  change (DFinsupp.single (β := fun j : Fin k ↦ Fin (p j) → K) i v) i = 0 at hz
  rw [DFinsupp.single_eq_same] at hz
  rw [hz, map_zero]

theorem coordinateComponent_finrank (p : Fin k → ℕ) (i : Fin k) :
    Module.finrank K (coordinateComponent (K := K) p i) = p i := by
  have hi : Function.Injective (DirectSum.lof K (Fin k) (fun j ↦ Fin (p j) → K) i) := by
    intro x y h
    have hc := congrArg (fun z : CoordinateSum K p ↦ z i) h
    simpa only [DirectSum.lof_eq_of, DirectSum.of_eq_same] using hc
  rw [coordinateComponent, LinearMap.finrank_range_of_inj hi, Module.finrank_fin_fun]

theorem coordinateSum_finrank (p : Fin k → ℕ) :
    Module.finrank K (CoordinateSum K p) = ∑ i, p i := by
  rw [Module.finrank_directSum]
  simp only [Module.finrank_fin_fun]

noncomputable def coordinateInternalDecomposition (p : Fin k → ℕ) (hp : ∀ i, 1 ≤ p i) :
    SizedInternalDecomposition K (CoordinateSum K p) p := by
  refine ⟨⟨coordinateComponent p,
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
      (coordinateComponents_iSupIndep p) (coordinateComponents_iSup p), ?_⟩, coordinateComponent_finrank p⟩
  intro i
  apply Submodule.one_le_finrank_iff.mp
  rw [coordinateComponent_finrank]
  exact hp i

variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- Produce an actual decomposition of V for every positive profile whose
sum is dim V, by transporting the canonical coordinate decomposition. -/
noncomputable def sizedInternalOfProfile (p : Fin k → ℕ) (hp : ∀ i, 1 ≤ p i)
    (hs : (∑ i, p i) = Module.finrank K V) : SizedInternalDecomposition K V p :=
  mapSizedInternal
    (LinearEquiv.ofFinrankEq (R := K) (CoordinateSum K p) V ((coordinateSum_finrank p).trans hs))
    (coordinateInternalDecomposition p hp)

theorem sizedInternal_nonempty_of_profile (p : Fin k → ℕ) (hp : ∀ i, 1 ≤ p i)
    (hs : (∑ i, p i) = Module.finrank K V) : Nonempty (SizedInternalDecomposition K V p) :=
  ⟨sizedInternalOfProfile p hp hs⟩

end BooleanAntichainsKernel
