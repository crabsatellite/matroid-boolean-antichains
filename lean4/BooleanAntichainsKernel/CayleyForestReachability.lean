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
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Pi
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Push
import Lean.Elab.Tactic.Omega

namespace Brockian.Cayley

open Finset

/-!
# Cayley's formula

The number of labeled trees on `n` vertices is `n ^ (n - 2)`.

The proof goes through *rooted forests*, encoded as "parent functions": a rooted forest on a
vertex set `A` with set of roots `S ⊆ A` is a function `f : V → V` which fixes everything
outside `A \ S`, maps `A \ S` into `A`, and such that iterating `f` from any vertex of `A`
eventually lands in `S`.

The main counting statement is
`|A| * #(forests on A with roots S) = |S| * |A| ^ (|A| - |S|)`,
proved by induction on `|A|` (deleting a root and summing over the set of its children).

Specialising to `A = univ` and `S = {0}` in `Fin n` and putting rooted forests with a single
root in bijection with trees gives Cayley's formula.
-/

/-! ### Rooted forests, encoded by parent functions -/

section Forest

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `IsForest A S f` says that `f` is the parent function of a rooted forest on the vertex
set `A` whose set of roots is `S`. -/
structure IsForest (A S : Finset V) (f : V → V) : Prop where
  /-- Vertices which are not non-root vertices of the forest are fixed. -/
  fixed : ∀ v, v ∉ A \ S → f v = v
  /-- The parent of a non-root vertex is a vertex. -/
  maps : ∀ v ∈ A \ S, f v ∈ A
  /-- Iterating the parent function eventually reaches a root. -/
  reaches : ∀ v ∈ A, ∃ m, f^[m] v ∈ S

/-- The finset of rooted forests on `A` with roots `S`, encoded by parent functions. -/
noncomputable def forestFinset (A S : Finset V) : Finset (V → V) :=
  @Finset.filter _ (IsForest A S) (Classical.decPred _) Finset.univ

@[simp] lemma mem_forestFinset {A S : Finset V} {f : V → V} :
    f ∈ forestFinset A S ↔ IsForest A S f := by
  classical
  simp [forestFinset]

/-- If all vertices are roots, the only forest is the identity. -/
lemma forestFinset_self (A : Finset V) : forestFinset A A = {id} := by
  ext f
  simp only [mem_forestFinset, Finset.mem_singleton]
  constructor
  · intro hf
    ext v
    exact hf.fixed v (by simp)
  · rintro rfl
    exact ⟨fun v _ => rfl, fun v hv => by simp at hv, fun v hv => ⟨0, hv⟩⟩

/-- With no roots and at least one vertex there is no forest. -/
lemma forestFinset_empty_roots {A : Finset V} (hA : A.Nonempty) : forestFinset A ∅ = ∅ := by
  ext f
  simp only [mem_forestFinset, Finset.notMem_empty, iff_false]
  rintro ⟨-, -, hreaches⟩
  obtain ⟨v, hv⟩ := hA
  obtain ⟨m, hm⟩ := hreaches v hv
  exact Finset.notMem_empty _ hm

/-! #### The two transport lemmas for reachability -/

omit [Fintype V] in
/-- Pushing reachability forward when the edges into `r` are cut. -/
lemma exists_iterate_mem_of_cut {f g : V → V} {C S S' : Finset V} {r : V}
    (hagree : ∀ v, v ∉ C → f v = g v) (hC : ∀ v ∈ C, f v = r) (hr : r ∈ S)
    (hS' : ∀ w ∈ S', w ∈ S ∨ w ∈ C) :
    ∀ (m : ℕ) (v : V), g^[m] v ∈ S' → ∃ m', f^[m'] v ∈ S := by
  -- First prove a helper: f^[k] v = g^[k] v as long as g^[i] v ∉ C for all i ≤ k
  have hagreem : ∀ k v, (∀ i ≤ k, g^[i] v ∉ C) → f^[k] v = g^[k] v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      intro v h
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      have hgk : g^[k] v ∉ C := h k (Nat.le_succ k)
      rw [ih v (fun i hi => h i (Nat.le_succ_of_le hi)), hagree (g^[k] v) hgk]
  intro m v hgS'
  by_cases halt : ∀ i ≤ m, g^[i] v ∉ C
  · -- All iterates up to m are outside C, so f^[m] v = g^[m] v
    have hfmgm : f^[m] v = g^[m] v := hagreem m v halt
    by_cases hS : g^[m] v ∈ S
    · exact ⟨m, hfmgm ▸ hS⟩
    · have hCm : g^[m] v ∈ C := by simpa [hS] using hS' _ hgS'
      have hCm' : f^[m] v ∈ C := by rw [hfmgm]; exact hCm
      exact ⟨m + 1, by rw [Function.iterate_succ_apply', show f (f^[m] v) = r from hC _ hCm']; exact hr⟩
  · -- Some iterate g^[i] v ∈ C for i ≤ m
    push Not at halt
    -- Find the first i where g^[i] v ∈ C
    let i := Nat.find halt
    have hi_bound : i ≤ m := (Nat.find_spec halt).1
    have hi_mem : g^[i] v ∈ C := (Nat.find_spec halt).2
    -- All earlier iterates are outside C
    have hi_min : ∀ j < i, g^[j] v ∉ C := fun j hj h =>
      (Nat.find_min halt hj ⟨(Nat.le_of_lt hj).trans hi_bound, h⟩)
    -- So f^[i] v = g^[i] v (using agreem for i-1, then one more step)
    have hf_eq : f^[i] v = g^[i] v := by
      rcases i with ⟨ ⟩
      · simp
      · rename_i k
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
        have hi_min' : ∀ j < k + 1, g^[j] v ∉ C := hi_min
        have hgik : g^[k] v ∉ C := hi_min' k (Nat.lt_succ_self k)
        rw [hagreem k v (fun j hj => hi_min' j (Nat.lt_of_le_of_lt hj (Nat.lt_succ_self k))),
            hagree (g^[k] v) hgik]
    -- Now use hf_eq and hi_mem to get f^[i+1] v = r ∈ S
    exact ⟨i + 1, by rw [Function.iterate_succ_apply', hf_eq]; rw [hC _ hi_mem]; exact hr⟩

omit [Fintype V] in
/-- Pulling reachability back when the edges into `r` are cut. -/
lemma exists_iterate_mem_of_cut' {f g : V → V} {C S S' : Finset V} {r : V}
    (hagree : ∀ v, v ∉ C → g v = f v) (hCS' : C ⊆ S') (hSr : ∀ w ∈ S, w ≠ r → w ∈ S')
    (hne : ∀ v, v ≠ r → v ∉ S → v ∉ C → f v ≠ r) :
    ∀ (m : ℕ) (v : V), v ≠ r → f^[m] v ∈ S → ∃ m', g^[m'] v ∈ S' := by
  intro m v hv hfm
  -- Key fact: if all iterates up to n are outside C, then g^[n] v = f^[n] v
  have iter_eq : ∀ n w, (∀ j < n, f^[j] w ∉ C) → g^[n] w = f^[n] w := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      intro w h
      simp only [Function.iterate_succ_apply']
      rw [ih _ fun j hj => h j (Nat.lt_succ_of_lt hj)]
      apply hagree
      exact h n (Nat.lt_succ_self n)
  -- Use classical choice to find the minimum k where f^[k] v ∈ S ∪ C
  have hex : ∃ k, k ≤ m ∧ f^[k] v ∈ S ∪ C := ⟨m, le_refl m, Finset.mem_union_left _ hfm⟩
  let k := Nat.find hex
  have hkP : k ≤ m ∧ f^[k] v ∈ S ∪ C := Nat.find_spec hex
  have hk_le : k ≤ m := hkP.1
  have hksC : f^[k] v ∈ S ∪ C := hkP.2
  -- All previous iterates are outside S ∪ C
  have hbefore : ∀ j < k, f^[j] v ∉ S ∪ C := fun j hj hmem => Nat.find_min hex hj ⟨by omega, hmem⟩
  use k
  -- Since j < k implies f^[j] v ∉ C, we have g^[k] v = f^[k] v
  rw [iter_eq k v fun j hj => by
    intro hfjc
    exact hbefore j hj (by simp [Finset.mem_union]; right; exact hfjc)]
  -- Now g^[k] v = f^[k] v ∈ S ∪ C
  have hksC' := Finset.mem_union.mp hksC
  rcases hksC' with hktS | hktC
  · -- f^[k] v ∈ S
    by_cases hktr : f^[k] v = r
    · -- f^[k] v = r, contradiction with minimality of k
      -- Use strong induction to show this leads to v = r
      exfalso
      have : v = r := by
        have hall : ∀ n ≤ k, f^[n] v = r → v = r := by
          intro n hn hnr
          induction n using Nat.strong_induction_on with
          | _ m ih =>
            by_cases hm0 : m = 0
            · simp [hm0] at hnr
              exact hnr
            · have hm_pos : m > 0 := Nat.pos_of_ne_zero hm0
              have hfnm1 : f (f^[m-1] v) = r := by
                have heq : f^[m] v = f (f^[m-1] v) := by
                  conv_lhs => rw [show m = Nat.succ (m - 1) by omega]
                  exact Function.iterate_succ_apply' f (m - 1) v
                rw [← heq]; exact hnr
              have := hne (f^[m-1] v)
              by_cases hfm1 : f^[m-1] v = r
              · exact ih (m - 1) (by omega) (by omega) hfm1
              · have hfm1_not_S : f^[m-1] v ∉ S := fun h => hbefore (m - 1) (by omega) (Finset.mem_union_left _ h)
                have hfm1_not_C : f^[m-1] v ∉ C := fun h => hbefore (m - 1) (by omega) (Finset.mem_union_right _ h)
                exact absurd hfnm1 (this hfm1 hfm1_not_S hfm1_not_C)
        exact hall k (le_refl k) hktr
      exact hv this
    · exact hSr _ hktS hktr
  · -- f^[k] v ∈ C ⊆ S'
    exact hCS' hktC

end Forest

end Brockian.Cayley
