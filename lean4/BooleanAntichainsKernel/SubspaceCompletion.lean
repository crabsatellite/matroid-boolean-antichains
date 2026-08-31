import BooleanAntichainsKernel.SubspaceTopProduct
import BooleanAntichainsKernel.SubspaceF23Values
import BooleanAntichainsKernel.HeightGapEndpoints
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.List.OfFn

namespace BooleanAntichainsKernel

open scoped Classical

theorem subspaceF23_count_of_value {k m : ℕ} (hk : 1 ≤ k)
    (hv : finiteSubspaceEnumerator 2 3 k = (m : ℚ)) :
    Fintype.card (BooleanAntichain k (Submodule (ZMod 2) (Fin 3 → ZMod 2))) = m := by
  have h := subspace_count_eq_bounded (ZMod 2) 3 k hk
  rw [ZMod.card, hv] at h
  exact_mod_cast h

/-- Every entry is an actual unordered antichain cardinality, obtained
from the general formula and kernel-reduced bounded profile sums. -/
theorem subspaceF23_distribution :
    List.ofFn (fun k : Fin 4 ↦ Fintype.card
      (BooleanAntichain k.1 (Submodule (ZMod 2) (Fin 3 → ZMod 2)))) = [1, 15, 49, 28] := by
  have h1 := subspaceF23_count_of_value (by decide) subspaceF23_singletons_value
  have h2 := subspaceF23_count_of_value (by decide) subspaceF23_pairs_value
  have h3 := subspaceF23_count_of_value (by decide) subspaceF23_triples_value
  change
    [Fintype.card (BooleanAntichain 0 (Submodule (ZMod 2) (Fin 3 → ZMod 2))),
     Fintype.card (BooleanAntichain 1 (Submodule (ZMod 2) (Fin 3 → ZMod 2))),
     Fintype.card (BooleanAntichain 2 (Submodule (ZMod 2) (Fin 3 → ZMod 2))),
     Fintype.card (BooleanAntichain 3 (Submodule (ZMod 2) (Fin 3 → ZMod 2)))] = [1, 15, 49, 28]
  rw [booleanAntichain_count_zero, h1, h2, h3]

end BooleanAntichainsKernel
