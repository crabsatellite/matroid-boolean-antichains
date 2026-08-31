/-
Cache partition of the complete Cayley proof from:
https://github.com/primaryhosting/brockian-mathematics/blob/313243c3c37ad150109cb057a062a72d73b4c260/Brockian/Cayley.lean
Pinned source blob: 111a5bdcd71501e5a207ed3a6fef7c26a64e6a3d
Adaptation: bounded imports and separately kernel-checked cache partitions.
The source's rooted-forest counting route and actual SimpleGraph.IsTree target are retained.

MIT License

Copyright (c) 2026 Christopher Brock

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/
import BooleanAntichainsKernel.CayleyForestCount
import BooleanAntichainsKernel.CayleyParentGraphs

namespace Brockian.Cayley

open Finset


/-- The trees on `Fin n` form a finite type: there are only finitely many simple graphs
on a finite vertex type. -/
noncomputable instance instFintypeTreeSubtype (n : ℕ) :
    Fintype {G : SimpleGraph (Fin n) // G.IsTree} := Fintype.ofFinite _

/-- Cayley's formula: the number of labeled trees on n ≥ 1 vertices is n^(n−2)
    (counted as spanning trees of the complete graph, i.e. connected acyclic simple graphs). -/
theorem cayley_formula (n : ℕ) (hn : 1 ≤ n) :
    Fintype.card {G : SimpleGraph (Fin n) // G.IsTree} = n ^ (n - 2) := by
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
  have hcard : Fintype.card {G : SimpleGraph (Fin (N + 1)) // G.IsTree}
      = (forestFinset (Finset.univ : Finset (Fin (N + 1))) {0}).card := by
    rw [← Nat.card_eq_fintype_card, card_tree_eq_card_forest, card_forest_subtype]
  have h := card_forestFinset (Finset.univ : Finset (Fin (N + 1))) {0} (by simp)
  simp only [Finset.card_univ, Fintype.card_fin, Finset.card_singleton, one_mul,
    Nat.add_sub_cancel] at h
  rw [hcard]
  refine Nat.eq_of_mul_eq_mul_left (show 0 < N + 1 by omega) ?_
  rw [h]
  rcases N with _ | N
  · simp
  · rw [show N + 1 + 1 - 2 = N by omega]
    ring

end Brockian.Cayley
