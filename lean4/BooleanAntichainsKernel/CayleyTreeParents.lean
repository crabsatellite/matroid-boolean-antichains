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
import BooleanAntichainsKernel.CayleyForestReachability
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Tactic.Ring

namespace Brockian.Cayley

open Finset

/-! ### From trees to rooted forests -/

section Graph

variable {N : ℕ} {G : SimpleGraph (Fin (N + 1))}

/-- The unique path from `v` to `0` in a tree. -/
noncomputable def treePath (hG : G.IsTree) (v : Fin (N + 1)) : G.Walk v 0 :=
  (hG.existsUnique_path v 0).choose

lemma treePath_isPath (hG : G.IsTree) (v : Fin (N + 1)) : (treePath hG v).IsPath :=
  (hG.existsUnique_path v 0).choose_spec.1

lemma treePath_unique (hG : G.IsTree) {v : Fin (N + 1)} (q : G.Walk v 0) (hq : q.IsPath) :
    q = treePath hG v :=
  (hG.existsUnique_path v 0).choose_spec.2 q hq

/-- The parent of `v` in a tree rooted at `0`: the second vertex of the unique path to `0`. -/
noncomputable def parent (hG : G.IsTree) (v : Fin (N + 1)) : Fin (N + 1) := (treePath hG v).snd

lemma parent_adj (hG : G.IsTree) {v : Fin (N + 1)} (hv : v ≠ 0) : G.Adj v (parent hG v) :=
  SimpleGraph.Walk.adj_snd (SimpleGraph.Walk.not_nil_of_ne hv)

lemma parent_zero (hG : G.IsTree) : parent hG 0 = 0 := by
  unfold parent treePath
  have h := (hG.existsUnique_path 0 0).choose_spec
  have padj : (default : G.Walk 0 0).IsPath := by simp
  have e := (h.2 default padj).symm
  simp only [e]
  rfl

lemma length_treePath_parent (hG : G.IsTree) {v : Fin (N + 1)} (hv : v ≠ 0) :
    (treePath hG (parent hG v)).length < (treePath hG v).length := by
  have hnil : ¬ (treePath hG v).Nil := SimpleGraph.Walk.not_nil_of_ne hv
  have h : (treePath hG v).tail = treePath hG (parent hG v) :=
    treePath_unique hG _ (treePath_isPath hG v).tail
  have hl := SimpleGraph.Walk.length_tail_add_one hnil
  rw [h] at hl
  -- `omega` is not used here: the two occurrences of the walk length differ in an
  -- implicit vertex argument (`parent hG v` vs `(treePath hG v).snd`), which is
  -- definitionally but not syntactically equal.
  exact lt_of_lt_of_le (Nat.lt_succ_self _) hl.le

lemma treePath_length_pos (hG : G.IsTree) {v : Fin (N + 1)} (hv : v ≠ 0) :
    0 < (treePath hG v).length :=
  SimpleGraph.Walk.not_nil_iff_lt_length.mp (SimpleGraph.Walk.not_nil_of_ne hv)

lemma parent_reaches_aux (hG : G.IsTree) : ∀ (k : ℕ) (v : Fin (N + 1)),
    (treePath hG v).length ≤ k → ∃ m, (parent hG)^[m] v = 0 := by
  intro k
  induction k with
  | zero =>
    intro v hv
    by_cases h0 : v = 0
    · exact ⟨0, by simp [h0]⟩
    · exact absurd (treePath_length_pos hG h0) (by omega)
  | succ k ih =>
    intro v hv
    by_cases h0 : v = 0
    · exact ⟨0, by simp [h0]⟩
    · have hlt := length_treePath_parent hG h0
      obtain ⟨m, hm⟩ := ih (parent hG v) (by omega)
      exact ⟨m + 1, by rw [Function.iterate_succ_apply]; exact hm⟩

lemma parent_reaches (hG : G.IsTree) (v : Fin (N + 1)) : ∃ m, (parent hG)^[m] v = 0 :=
  parent_reaches_aux hG _ v le_rfl

lemma isForest_parent (hG : G.IsTree) :
    IsForest (Finset.univ : Finset (Fin (N + 1))) {0} (parent hG) := by
  refine ⟨fun v hv => ?_, fun v _ => Finset.mem_univ _, fun v _ => ?_⟩
  · simp only [Finset.sdiff_singleton_eq_erase, Finset.mem_erase, Finset.mem_univ, and_true,
      not_not] at hv
    subst hv
    exact parent_zero hG
  · obtain ⟨m, hm⟩ := parent_reaches hG v
    exact ⟨m, by simp [hm]⟩

/-- If `p (p v) = v` then the orbit of `v` under `p` is `{v, p v}`. -/
lemma iterate_eq_of_two_cycle {V : Type*} {p : V → V} {v : V} (h : p (p v) = v) (m : ℕ) :
    p^[m] v = v ∨ p^[m] v = p v := by
  have heven : ∀ k, p^[k + k] v = v := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      calc p^[k + 1 + (k + 1)] v
          = p^[k + k + 2] v := by ring_nf
        _ = p^[k + k + 1 + 1] v := by ring_nf
        _ = p (p^[k + k + 1] v) := by rw [Function.iterate_succ']; rfl
        _ = p (p (p^[k + k] v)) := by rw [Function.iterate_succ']; rfl
        _ = p (p v) := by rw [ih]
        _ = v := h
  have hodd : ∀ k, p^[2 * k + 1] v = p v := by
    intro k
    rw [Function.iterate_succ']
    show p (p^[2 * k] v) = p v
    have : 2 * k = k + k := by ring
    rw [this, heven k]
  rcases Nat.even_or_odd m with ⟨k, hk⟩ | ⟨k, hk⟩
  · left; rw [hk]; exact heven k
  · right; rw [hk]; exact hodd k

/-- In a rooted forest with a single root `0`, the parent function has no `2`-cycle. -/
lemma not_two_cycle {p : Fin (N + 1) → Fin (N + 1)}
    (hp : IsForest (Finset.univ : Finset (Fin (N + 1))) {0} p) {v : Fin (N + 1)} (hv : v ≠ 0)
    (h : p (p v) = v) : False := by
  obtain ⟨m, hm⟩ := hp.reaches v (Finset.mem_univ v)
  rw [Finset.mem_singleton] at hm
  have hp0 : p 0 = 0 := hp.fixed 0 (by simp)
  rcases iterate_eq_of_two_cycle h m with h' | h'
  · exact hv (h' ▸ hm)
  · have : p v = 0 := h' ▸ hm
    rw [this, hp0] at h
    exact hv h.symm

lemma parent_ne_self {p : Fin (N + 1) → Fin (N + 1)}
    (hp : IsForest (Finset.univ : Finset (Fin (N + 1))) {0} p) {v : Fin (N + 1)} (hv : v ≠ 0) :
    p v ≠ v := fun hc => not_two_cycle hp hv (by rw [hc, hc])

/-- The map `v ↦ s(v, p v)` is injective away from the root, for a rooted forest `p`. -/
lemma injOn_edge_of_isForest {p : Fin (N + 1) → Fin (N + 1)}
    (hp : IsForest (Finset.univ : Finset (Fin (N + 1))) {0} p) :
    Set.InjOn (fun v => s(v, p v)) {v : Fin (N + 1) | v ≠ 0} := by
  intro v hv w hw h
  simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at h
  rcases h with ⟨h1, -⟩ | ⟨h1, h2⟩
  · exact h1
  · exact absurd (by rw [h2, h1] : p (p v) = v) (fun hc => (not_two_cycle hp hv hc).elim)

lemma ncard_edges_image {p : Fin (N + 1) → Fin (N + 1)}
    (hp : IsForest (Finset.univ : Finset (Fin (N + 1))) {0} p) :
    ((fun v => s(v, p v)) '' {v : Fin (N + 1) | v ≠ 0}).ncard = N := by
  rw [Set.InjOn.ncard_image (injOn_edge_of_isForest hp)]
  have h : {v : Fin (N + 1) | v ≠ 0} = ↑((Finset.univ : Finset (Fin (N + 1))).erase 0) := by
    ext v; simp
  rw [h, Set.ncard_coe_finset, Finset.card_erase_of_mem (Finset.mem_univ _)]
  simp

/-- The edges of a tree are exactly the edges from a vertex to its parent. -/
lemma edgeSet_eq_of_isTree (hG : G.IsTree) :
    G.edgeSet = (fun v => s(v, parent hG v)) '' {v : Fin (N + 1) | v ≠ 0} := by
  have hsub : (fun v => s(v, parent hG v)) '' {v : Fin (N + 1) | v ≠ 0} ⊆ G.edgeSet := by
    rintro e ⟨v, hv, rfl⟩
    exact parent_adj hG hv
  have hcard : G.edgeSet.ncard = N := by
    have h := (SimpleGraph.isTree_iff_connected_and_card.mp hG).2
    rw [Nat.card_coe_set_eq] at h
    simpa using h
  refine (Set.eq_of_subset_of_ncard_le hsub ?_ (Set.toFinite _)).symm
  rw [hcard, ncard_edges_image (isForest_parent hG)]

lemma tree_parent_injective :
    Function.Injective (fun T : {G : SimpleGraph (Fin (N + 1)) // G.IsTree} => parent T.2) := by
  rintro ⟨G₁, h₁⟩ ⟨G₂, h₂⟩ h
  simp only at h
  refine Subtype.ext ?_
  rw [← SimpleGraph.edgeSet_inj, edgeSet_eq_of_isTree h₁, edgeSet_eq_of_isTree h₂, h]

end Graph

end Brockian.Cayley
