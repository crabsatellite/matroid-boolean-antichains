import BooleanAntichainsKernel.ProjectiveLattice
import Mathlib.Algebra.GroupWithZero.Units.Fintype

namespace BooleanAntichainsKernel

open Finset
open scoped Classical

abbrev OrderedProjectiveFrame (K V : Type*) [Field K] [AddCommGroup V] [Module K V] (k : ℕ) :=
  {p : Fin k → Projectivization K V // Projectivization.Independent p}

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {k : ℕ}

noncomputable instance [Fintype V] : Fintype (OrderedProjectiveFrame K V k) := Subtype.fintype _

theorem orderedProjectiveFrame_injective (p : OrderedProjectiveFrame K V k) :
    Function.Injective p.1 := by
  intro i j h
  exact (Projectivization.independent_iff.mp p.2).injective (congrArg Projectivization.rep h)

/-- Multiply each actual projective representative by an independently
chosen nonzero scalar; independence is preserved, not assumed. -/
noncomputable def projectiveFrameLift (x : OrderedProjectiveFrame K V k × (Fin k → Kˣ)) :
    IndependentFrame K V k :=
  ⟨fun i ↦ x.2 i • (x.1.1 i).rep,
    (Projectivization.independent_iff.mp x.1.2).units_smul x.2⟩

def projectiveFrameOfVectors (v : IndependentFrame K V k) : OrderedProjectiveFrame K V k :=
  ⟨fun i ↦ Projectivization.mk K (v.1 i) (v.2.ne_zero i),
    Projectivization.Independent.mk v.1 (fun i ↦ v.2.ne_zero i) v.2⟩

theorem projectiveFrameOfVectors_lift (p : OrderedProjectiveFrame K V k) (a : Fin k → Kˣ) :
    projectiveFrameOfVectors (projectiveFrameLift (p, a)) = p := by
  apply Subtype.ext
  funext i
  calc
    _ = Projectivization.mk K (p.1 i).rep (p.1 i).rep_nonzero :=
      (Projectivization.mk_eq_mk_iff K _ _ _ _).mpr ⟨a i, rfl⟩
    _ = p.1 i := Projectivization.mk_rep (p.1 i)

theorem projectiveFrameLift_injective : Function.Injective
    (projectiveFrameLift (K := K) (V := V) (k := k)) := by
  rintro ⟨p, a⟩ ⟨q, b⟩ h
  have hpq : p = q := (projectiveFrameOfVectors_lift p a).symm.trans
    ((congrArg projectiveFrameOfVectors h).trans (projectiveFrameOfVectors_lift q b))
  subst q
  have hab : a = b := by
    funext i
    apply Units.ext
    exact smul_left_injective K (p.1 i).rep_nonzero
      (congrArg (fun v : IndependentFrame K V k ↦ v.1 i) h)
  subst b
  rfl

theorem projectiveFrameLift_surjective : Function.Surjective
    (projectiveFrameLift (K := K) (V := V) (k := k)) := by
  intro v
  let p := projectiveFrameOfVectors v
  have hs : ∀ i, ∃ a : Kˣ, a • (p.1 i).rep = v.1 i := by
    intro i
    exact (Projectivization.mk_eq_mk_iff K _ _ (v.2.ne_zero i) (p.1 i).rep_nonzero).mp
      (Projectivization.mk_rep (p.1 i)).symm
  choose a ha using hs
  exact ⟨(p, a), Subtype.ext (funext ha)⟩

/-- The scalar fibre is the full product of k copies of Kˣ, with actual
inverse maps; it is not a postulated (q-1)^k multiplicity. -/
noncomputable def projectiveFrameScalarEquiv :
    (OrderedProjectiveFrame K V k × (Fin k → Kˣ)) ≃ IndependentFrame K V k :=
  Equiv.ofBijective projectiveFrameLift
    ⟨projectiveFrameLift_injective, projectiveFrameLift_surjective⟩

theorem projectiveFrameScalarEquiv_apply
    (p : OrderedProjectiveFrame K V k) (a : Fin k → Kˣ) (i : Fin k) :
    (projectiveFrameScalarEquiv (p, a)).1 i = a i • (p.1 i).rep := rfl

variable [Fintype K] [Fintype V]

theorem projectiveFrame_scalar_count :
    Fintype.card (IndependentFrame K V k) =
      Fintype.card (OrderedProjectiveFrame K V k) * (Fintype.card K - 1) ^ k := by
  rw [← Fintype.card_congr (projectiveFrameScalarEquiv (K := K) (V := V) (k := k)),
    Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Fintype.card_units]

theorem projectiveFrame_count_rational (hk : k ≤ Module.finrank K V) :
    (Fintype.card (OrderedProjectiveFrame K V k) : ℚ) =
      (frameProduct (Fintype.card K) (Module.finrank K V) k : ℚ) /
        (((Fintype.card K - 1 : ℕ) : ℚ) ^ k) := by
  have hz : (((Fintype.card K - 1 : ℕ) : ℚ) ^ k) ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.mpr (Nat.ne_of_gt
      (Nat.sub_pos_of_lt (Fintype.one_lt_card (α := K)))))
  apply (eq_div_iff hz).mpr
  have h := projectiveFrame_scalar_count (K := K) (V := V) (k := k)
  rw [independentFrame_card hk] at h
  exact_mod_cast h.symm

end BooleanAntichainsKernel
