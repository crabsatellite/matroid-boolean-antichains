import BooleanAntichainsKernel.FinitePartitionSetoid
import Mathlib.SetTheory.Cardinal.Finite

namespace BooleanAntichainsKernel

open scoped Classical

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The missing finite join is the least common coarsening. The existing
native refinement order and intersection-block meet are retained. -/
noncomputable instance finitePartitionLattice :
    Lattice (Finpartition (Finset.univ : Finset α)) where
  toSemilatticeInf := inferInstance
  sup P Q := Finpartition.ofSetoid (finitePartitionSetoid P ⊔ finitePartitionSetoid Q)
  le_sup_left P Q := (finitePartitionSetoid_le_iff P _).mp (by
    rw [finitePartitionSetoid_ofSetoid]
    exact le_sup_left)
  le_sup_right P Q := (finitePartitionSetoid_le_iff Q _).mp (by
    rw [finitePartitionSetoid_ofSetoid]
    exact le_sup_right)
  sup_le P Q R hPR hQR := (finitePartitionSetoid_le_iff _ R).mp (by
    rw [finitePartitionSetoid_ofSetoid]
    exact sup_le ((finitePartitionSetoid_le_iff P R).mpr hPR)
      ((finitePartitionSetoid_le_iff Q R).mpr hQR))

theorem finitePartition_inf_blocks (P Q : Finpartition (Finset.univ : Finset α)) :
    (P ⊓ Q).parts = ((P.parts ×ˢ Q.parts).image fun B ↦ B.1 ∩ B.2).erase ∅ := rfl

theorem finitePartition_sup_setoid (P Q : Finpartition (Finset.univ : Finset α)) :
    finitePartitionSetoid (P ⊔ Q) = finitePartitionSetoid P ⊔ finitePartitionSetoid Q :=
  finitePartitionSetoid_ofSetoid _

theorem finitePartitionSetoidOrderIso_top :
    finitePartitionSetoidOrderIso (⊤ : Finpartition (Finset.univ : Finset α)) = ⊤ :=
  map_top finitePartitionSetoidOrderIso

theorem finitePartitionSetoidOrderIso_bot :
    finitePartitionSetoidOrderIso (⊥ : Finpartition (Finset.univ : Finset α)) = ⊥ :=
  map_bot finitePartitionSetoidOrderIso

/-- Send an actual equivalence class to its literal finite block. -/
def finitePartitionQuotientToBlock (P : Finpartition (Finset.univ : Finset α)) :
    Quotient (finitePartitionSetoid P) → P.parts :=
  Quotient.lift (fun x ↦ ⟨P.part x, P.part_mem.mpr (Finset.mem_univ x)⟩)
    (fun _ _ h ↦ Subtype.ext h)

noncomputable def finitePartitionBlockToQuotient (P : Finpartition (Finset.univ : Finset α))
    (B : P.parts) : Quotient (finitePartitionSetoid P) :=
  Quotient.mk (finitePartitionSetoid P) (P.nonempty_of_mem_parts B.2).choose

theorem finitePartitionQuotientBlock_left (P : Finpartition (Finset.univ : Finset α))
    (q : Quotient (finitePartitionSetoid P)) :
    finitePartitionBlockToQuotient P (finitePartitionQuotientToBlock P q) = q := by
  induction q using Quotient.inductionOn with
  | h x =>
    apply Quotient.sound
    apply (finitePartitionSetoid_rel P _ x).mpr
    exact (P.nonempty_of_mem_parts (P.part_mem.mpr (Finset.mem_univ x))).choose_spec

theorem finitePartitionQuotientBlock_right (P : Finpartition (Finset.univ : Finset α))
    (B : P.parts) :
    finitePartitionQuotientToBlock P (finitePartitionBlockToQuotient P B) = B := by
  apply Subtype.ext
  exact P.part_eq_of_mem B.2 (P.nonempty_of_mem_parts B.2).choose_spec

noncomputable def finitePartitionQuotientBlockEquiv (P : Finpartition (Finset.univ : Finset α)) :
    Quotient (finitePartitionSetoid P) ≃ P.parts where
  toFun := finitePartitionQuotientToBlock P
  invFun := finitePartitionBlockToQuotient P
  left_inv := finitePartitionQuotientBlock_left P
  right_inv := finitePartitionQuotientBlock_right P

theorem finitePartitionQuotientBlockEquiv_mk (P : Finpartition (Finset.univ : Finset α)) (x : α) :
    (finitePartitionQuotientBlockEquiv P (Quotient.mk (finitePartitionSetoid P) x)).1 = P.part x := rfl

theorem finitePartition_block_count (P : Finpartition (Finset.univ : Finset α)) :
    Nat.card (Quotient (finitePartitionSetoid P)) = P.parts.card := by
  calc
    _ = Nat.card P.parts := Nat.card_congr (finitePartitionQuotientBlockEquiv P)
    _ = _ := by simp only [Nat.card_eq_fintype_card, Fintype.card_coe]

end BooleanAntichainsKernel
