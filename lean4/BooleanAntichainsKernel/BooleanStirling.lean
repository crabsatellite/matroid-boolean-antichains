import BooleanAntichainsKernel.BooleanProductRecurrence
import BooleanAntichainsKernel.LatticeTransport
import Mathlib.Data.Finset.Sum
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Combinatorics.Enumerative.Stirling

namespace BooleanAntichainsKernel

open Finset
open scoped Classical

def finsetGroundOrderIso {α β : Type*} (e : α ≃ β) : Finset α ≃o Finset β where
  toEquiv := e.finsetCongr
  map_rel_iff' := by
    intro S T
    exact Finset.map_subset_map

/-- Separate the last actual ground element. The source's Boolean product
identification is transported to antichains through this order isomorphism. -/
def booleanSuccProductOrderIso (n : ℕ) :
    Finset (Fin (n + 1)) ≃o Finset (Fin n) × Finset (Fin 1) :=
  (finsetGroundOrderIso (finSumFinEquiv : Fin n ⊕ Fin 1 ≃ Fin (n + 1)).symm).trans
    Finset.sumEquiv

theorem booleanLattice_count_recurrence (n k : ℕ) :
    Fintype.card (BooleanAntichain (k + 1) (Finset (Fin (n + 1)))) =
      (k + 2) * Fintype.card (BooleanAntichain (k + 1) (Finset (Fin n))) +
        Fintype.card (BooleanAntichain k (Finset (Fin n))) := by
  rw [Fintype.card_congr (booleanAntichainOrderIsoEquiv (booleanSuccProductOrderIso n) (k + 1))]
  exact product_booleanOne_recurrence k

/-- The total count cited in the Boolean-lattice corollary, proved from the
paper's own product recurrence and the singleton-lattice initial layer.
No reference result, count adapter or finite regression supplies this value. -/
theorem booleanLattice_count_stirling (n k : ℕ) :
    Fintype.card (BooleanAntichain k (Finset (Fin n))) = Nat.stirlingSecond (n + 1) (k + 1) := by
  induction n generalizing k with
  | zero =>
    cases k with
    | zero => simp [booleanAntichain_count_zero, Nat.stirlingSecond_one_right]
    | succ k =>
      rw [booleanZero_count_succ, Nat.stirlingSecond_eq_zero_of_lt (by omega)]
  | succ n ih =>
    cases k with
    | zero => simp [booleanAntichain_count_zero, Nat.stirlingSecond_one_right]
    | succ k =>
      rw [booleanLattice_count_recurrence, ih, ih]
      exact (Nat.stirlingSecond_succ_succ (n + 1) (k + 1)).symm

end BooleanAntichainsKernel
