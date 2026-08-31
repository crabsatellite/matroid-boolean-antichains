import BooleanAntichainsKernel.FinitePartitionLattice
import Mathlib.Order.Hom.Set

namespace BooleanAntichainsKernel

open scoped Classical

variable {α β : Type*}

/-- Exact relation transport along an already proved carrier equivalence. -/
def setoidTransportOrderIso (e : α ≃ β) : Setoid α ≃o Setoid β where
  toFun r := r.comap e.symm
  invFun s := s.comap e
  left_inv r := by
    apply Setoid.ext
    intro x y
    change r (e.symm (e x)) (e.symm (e y)) ↔ r x y
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  right_inv s := by
    apply Setoid.ext
    intro x y
    change s (e (e.symm x)) (e (e.symm y)) ↔ s x y
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  map_rel_iff' := by
    intro r s
    constructor
    · intro h x y hxy
      have hr : (r.comap e.symm) (e x) (e y) := by
        change r (e.symm (e x)) (e.symm (e y))
        simpa only [Equiv.symm_apply_apply] using hxy
      have hs := h hr
      change s (e.symm (e x)) (e.symm (e y)) at hs
      simpa only [Equiv.symm_apply_apply] using hs
    · intro h x y hxy
      exact h hxy

theorem setoidTransportOrderIso_rel (e : α ≃ β) (r : Setoid α) (x y : α) :
    setoidTransportOrderIso e r (e x) (e y) ↔ r x y := by
  change r (e.symm (e x)) (e.symm (e y)) ↔ r x y
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]

variable [Fintype α] [DecidableEq α]

/-- The original block containing an original vertex. -/
def finitePartitionBlockOf (P : Finpartition (Finset.univ : Finset α)) (x : α) : P.parts :=
  ⟨P.part x, P.part_mem.mpr (Finset.mem_univ x)⟩

theorem finitePartitionBlockOf_surjective (P : Finpartition (Finset.univ : Finset α)) :
    Function.Surjective (finitePartitionBlockOf P) := by
  intro B
  obtain ⟨x, hx⟩ := P.nonempty_of_mem_parts B.2
  exact ⟨x, Subtype.ext (P.part_eq_of_mem B.2 hx)⟩

theorem finitePartitionBlockOf_eq_iff (P : Finpartition (Finset.univ : Finset α)) (x y : α) :
    finitePartitionBlockOf P x = finitePartitionBlockOf P y ↔ finitePartitionSetoid P x y :=
  Subtype.ext_iff

theorem finitePartitionBlockOf_ker (P : Finpartition (Finset.univ : Finset α)) :
    Setoid.ker (finitePartitionBlockOf P) = finitePartitionSetoid P :=
  Setoid.ext (fun x y ↦ finitePartitionBlockOf_eq_iff P x y)

/-- Coarsenings of P are precisely equivalence relations on its actual
blocks. The intermediate quotient is transported by the proved
quotient/block equivalence, not an unproved identification. -/
noncomputable def partitionCoarseningSetoidOrderIso (P : Finpartition (Finset.univ : Finset α)) :
    Set.Ici P ≃o Setoid P.parts :=
  (finitePartitionSetoidOrderIso.Ici P).trans
    ((Setoid.correspondence (finitePartitionSetoid P)).trans
      (setoidTransportOrderIso (finitePartitionQuotientBlockEquiv P)))

theorem partitionCoarseningSetoidOrderIso_rel (P : Finpartition (Finset.univ : Finset α))
    (Q : Set.Ici P) (x y : α) :
    partitionCoarseningSetoidOrderIso P Q (finitePartitionBlockOf P x) (finitePartitionBlockOf P y) ↔
      finitePartitionSetoid Q.1 x y := by
  change (Setoid.correspondence (finitePartitionSetoid P) ((finitePartitionSetoidOrderIso.Ici P) Q))
    ((finitePartitionQuotientBlockEquiv P).symm
      (finitePartitionQuotientBlockEquiv P (Quotient.mk (finitePartitionSetoid P) x)))
    ((finitePartitionQuotientBlockEquiv P).symm
      (finitePartitionQuotientBlockEquiv P (Quotient.mk (finitePartitionSetoid P) y))) ↔ _
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  rfl

theorem partitionCoarseningSetoidOrderIso_symm_rel (P : Finpartition (Finset.univ : Finset α))
    (r : Setoid P.parts) (x y : α) :
    finitePartitionSetoid ((partitionCoarseningSetoidOrderIso P).symm r).1 x y ↔
      r (finitePartitionBlockOf P x) (finitePartitionBlockOf P y) := by
  have h := partitionCoarseningSetoidOrderIso_rel P ((partitionCoarseningSetoidOrderIso P).symm r) x y
  rw [OrderIso.apply_symm_apply] at h
  exact h.symm

/-- The finite-block version of the quotient correspondence. -/
noncomputable def partitionCoarseningOrderIso (P : Finpartition (Finset.univ : Finset α)) :
    Set.Ici P ≃o Finpartition (Finset.univ : Finset P.parts) :=
  (partitionCoarseningSetoidOrderIso P).trans (finitePartitionSetoidOrderIso (α := P.parts)).symm

theorem partitionCoarseningOrderIso_rel (P : Finpartition (Finset.univ : Finset α))
    (Q : Set.Ici P) (x y : α) :
    finitePartitionSetoid (partitionCoarseningOrderIso P Q) (finitePartitionBlockOf P x)
      (finitePartitionBlockOf P y) ↔ finitePartitionSetoid Q.1 x y := by
  change finitePartitionSetoid (Finpartition.ofSetoid (partitionCoarseningSetoidOrderIso P Q))
    (finitePartitionBlockOf P x) (finitePartitionBlockOf P y) ↔ _
  rw [finitePartitionSetoid_ofSetoid]
  exact partitionCoarseningSetoidOrderIso_rel P Q x y

theorem partitionCoarseningOrderIso_same_block (P : Finpartition (Finset.univ : Finset α))
    (Q : Set.Ici P) (x y : α) :
    (∃ B ∈ (partitionCoarseningOrderIso P Q).parts,
      finitePartitionBlockOf P x ∈ B ∧ finitePartitionBlockOf P y ∈ B) ↔
    ∃ B ∈ Q.1.parts, x ∈ B ∧ y ∈ B := by
  rw [← finitePartitionSetoid_same_block, ← finitePartitionSetoid_same_block]
  exact partitionCoarseningOrderIso_rel P Q x y

end BooleanAntichainsKernel
