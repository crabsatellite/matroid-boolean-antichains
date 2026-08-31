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
import BooleanAntichainsKernel.CayleyTreeParents

namespace Brockian.Cayley

open Finset

section Graph

variable {N : ℕ} {G : SimpleGraph (Fin (N + 1))}

/-! ### From rooted forests to trees -/

/-- The graph associated with a parent function. -/
def graphOf (p : Fin (N + 1) → Fin (N + 1)) : SimpleGraph (Fin (N + 1)) :=
  SimpleGraph.fromRel (fun v w => v ≠ 0 ∧ p v = w)

lemma graphOf_adj {p : Fin (N + 1) → Fin (N + 1)} {v w : Fin (N + 1)} :
    (graphOf p).Adj v w ↔ v ≠ w ∧ ((v ≠ 0 ∧ p v = w) ∨ (w ≠ 0 ∧ p w = v)) := by
  simp [graphOf, SimpleGraph.fromRel]

lemma graphOf_adj_parent {p : Fin (N + 1) → Fin (N + 1)}
    (hp : IsForest (Finset.univ : Finset (Fin (N + 1))) {0} p) {v : Fin (N + 1)} (hv : v ≠ 0) :
    (graphOf p).Adj v (p v) :=
  graphOf_adj.mpr ⟨fun hc => parent_ne_self hp hv hc.symm, Or.inl ⟨hv, rfl⟩⟩

lemma graphOf_reachable_zero {p : Fin (N + 1) → Fin (N + 1)}
    (hp : IsForest (Finset.univ : Finset (Fin (N + 1))) {0} p) :
    ∀ (m : ℕ) (v : Fin (N + 1)), p^[m] v = 0 → (graphOf p).Reachable v 0 := by
  intro m
  induction m with
  | zero =>
    intro v hv
    simp only [Function.iterate_zero, id_eq] at hv
    subst hv
    rfl
  | succ m ih =>
    intro v hv
    by_cases h0 : v = 0
    · subst h0; rfl
    · have hpv : p^[m] (p v) = 0 := by rw [← Function.iterate_succ_apply]; exact hv
      exact ((graphOf_adj_parent hp h0).reachable).trans (ih (p v) hpv)

lemma graphOf_reachable_zero' {p : Fin (N + 1) → Fin (N + 1)}
    (hp : IsForest (Finset.univ : Finset (Fin (N + 1))) {0} p) (v : Fin (N + 1)) :
    (graphOf p).Reachable v 0 := by
  obtain ⟨m, hm⟩ := hp.reaches v (Finset.mem_univ v)
  exact graphOf_reachable_zero hp m v (by simpa using hm)

lemma graphOf_connected {p : Fin (N + 1) → Fin (N + 1)}
    (hp : IsForest (Finset.univ : Finset (Fin (N + 1))) {0} p) : (graphOf p).Connected := by
  haveI : Nonempty (Fin (N + 1)) := ⟨0⟩
  exact SimpleGraph.Connected.mk fun u v =>
    (graphOf_reachable_zero' hp u).trans (graphOf_reachable_zero' hp v).symm

lemma edgeSet_graphOf {p : Fin (N + 1) → Fin (N + 1)}
    (hp : IsForest (Finset.univ : Finset (Fin (N + 1))) {0} p) :
    (graphOf p).edgeSet = (fun v => s(v, p v)) '' {v : Fin (N + 1) | v ≠ 0} := by
  ext e
  induction e using Sym2.ind with
  | _ v w =>
  simp only [SimpleGraph.mem_edgeSet, graphOf_adj, Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hne, ⟨hv0, rfl⟩ | ⟨hw0, rfl⟩⟩
    · exact ⟨v, hv0, rfl⟩
    · exact ⟨w, hw0, Sym2.eq_swap⟩
  · rintro ⟨u, hu, he⟩
    rw [Sym2.eq_iff] at he
    rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨fun hc => parent_ne_self hp hu hc.symm, Or.inl ⟨hu, rfl⟩⟩
    · exact ⟨fun hc => parent_ne_self hp hu hc, Or.inr ⟨hu, rfl⟩⟩

lemma graphOf_isTree {p : Fin (N + 1) → Fin (N + 1)}
    (hp : IsForest (Finset.univ : Finset (Fin (N + 1))) {0} p) : (graphOf p).IsTree := by
  refine SimpleGraph.isTree_iff_connected_and_card.mpr ⟨graphOf_connected hp, ?_⟩
  rw [Nat.card_coe_set_eq, edgeSet_graphOf hp, ncard_edges_image hp]
  simp

lemma graphOf_injOn_aux {p q : Fin (N + 1) → Fin (N + 1)}
    (hp : IsForest (Finset.univ : Finset (Fin (N + 1))) {0} p)
    (hq : IsForest (Finset.univ : Finset (Fin (N + 1))) {0} q)
    (h : graphOf p = graphOf q) :
    ∀ (m : ℕ) (v : Fin (N + 1)), p^[m] v = 0 → p v = q v := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro v hv
  by_cases h0 : v = 0
  · subst h0
    rw [hp.fixed 0 (by simp), hq.fixed 0 (by simp)]
  · have hadj : (graphOf q).Adj v (p v) := h ▸ graphOf_adj_parent hp h0
    obtain ⟨hne, hcase⟩ := graphOf_adj.mp hadj
    rcases hcase with ⟨-, h1⟩ | ⟨hpv0, h2⟩
    · exact h1.symm
    · obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := by
        cases m with
        | zero => exact absurd hv h0
        | succ j => exact ⟨j, rfl⟩
      have hj : p^[j] (p v) = 0 := by rw [← Function.iterate_succ_apply]; exact hv
      have hpp : p (p v) = v := by rw [ih j (by omega) (p v) hj, h2]
      exact absurd hpp (fun hc => (not_two_cycle hp h0 hc).elim)

lemma graphOf_injOn {p q : Fin (N + 1) → Fin (N + 1)}
    (hp : IsForest (Finset.univ : Finset (Fin (N + 1))) {0} p)
    (hq : IsForest (Finset.univ : Finset (Fin (N + 1))) {0} q)
    (h : graphOf p = graphOf q) : p = q := by
  funext v
  obtain ⟨m, hm⟩ := hp.reaches v (Finset.mem_univ v)
  exact graphOf_injOn_aux hp hq h m v (by simpa using hm)

/-! ### The bijection -/

lemma card_tree_eq_card_forest :
    Nat.card {G : SimpleGraph (Fin (N + 1)) // G.IsTree}
      = Nat.card {p : Fin (N + 1) → Fin (N + 1) //
          IsForest (Finset.univ : Finset (Fin (N + 1))) {0} p} := by
  refine le_antisymm (Nat.card_le_card_of_injective
      (fun T => ⟨parent T.2, isForest_parent T.2⟩) ?_)
    (Nat.card_le_card_of_injective (fun P => ⟨graphOf P.1, graphOf_isTree P.2⟩) ?_)
  · intro T₁ T₂ h
    exact tree_parent_injective (congrArg Subtype.val h)
  · intro P₁ P₂ h
    exact Subtype.ext (graphOf_injOn P₁.2 P₂.2 (congrArg Subtype.val h))

lemma card_forest_subtype :
    Nat.card {p : Fin (N + 1) → Fin (N + 1) //
        IsForest (Finset.univ : Finset (Fin (N + 1))) {0} p}
      = (forestFinset (Finset.univ : Finset (Fin (N + 1))) {0}).card := by
  rw [← Nat.card_eq_finsetCard]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun p => mem_forestFinset.symm)

end Graph

end Brockian.Cayley
