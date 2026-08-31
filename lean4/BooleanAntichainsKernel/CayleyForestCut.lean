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
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Tauto

namespace Brockian.Cayley

open Finset

section Forest

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! #### Cutting the edges into a root -/

/-- Cut the edges going into the root `r`: the children `C` of `r` become roots. -/
def cut (C : Finset V) (f : V → V) : V → V := fun v => if v ∈ C then v else f v

/-- Reattach the vertices of `C` to the root `r`. -/
def uncut (C : Finset V) (r : V) (g : V → V) : V → V := fun v => if v ∈ C then r else g v

/-- The set of children of the root `r` in the forest `f`. -/
def children (A S : Finset V) (r : V) (f : V → V) : Finset V := (A \ S).filter (fun v => f v = r)

omit [Fintype V] in
lemma children_subset {A S : Finset V} {r : V} {f : V → V} : children A S r f ⊆ A \ S :=
  Finset.filter_subset _ _

omit [Fintype V] in
lemma isForest_cut {A S : Finset V} {r : V} (hr : r ∈ S) {f : V → V}
    (hf : IsForest A S f) :
    IsForest (A.erase r) (S.erase r ∪ children A S r f) (cut (children A S r f) f) := by
  set C := children A S r f with hCdef
  have hmemC : ∀ v, v ∈ C ↔ (v ∈ A ∧ v ∉ S ∧ f v = r) := by
    intro v
    simp [hCdef, children, Finset.mem_filter, Finset.mem_sdiff, and_assoc]
  have hset : ∀ v, v ∈ (A.erase r) \ (S.erase r ∪ C) ↔ (v ∈ A ∧ v ∉ S ∧ v ∉ C) := by
    intro v
    constructor
    · intro h
      simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_union, not_or] at h
      exact ⟨h.1.2, fun hvS => h.2.1 ⟨h.1.1, hvS⟩, h.2.2⟩
    · rintro ⟨h1, h2, h3⟩
      have hvr : v ≠ r := fun hh => h2 (hh ▸ hr)
      simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_union, not_or]
      exact ⟨⟨hvr, h1⟩, fun hcon => h2 hcon.2, h3⟩
  refine ⟨fun v hv => ?_, fun v hv => ?_, fun v hv => ?_⟩
  · by_cases hvC : v ∈ C
    · simp [cut, hvC]
    · have : v ∉ A \ S := by
        intro hcon
        exact hv ((hset v).2 ⟨(Finset.mem_sdiff.mp hcon).1, (Finset.mem_sdiff.mp hcon).2, hvC⟩)
      simp [cut, hvC, hf.fixed v this]
  · obtain ⟨hvA, hvS, hvC⟩ := (hset v).1 hv
    have hfv : f v ∈ A := hf.maps v (Finset.mem_sdiff.mpr ⟨hvA, hvS⟩)
    have hne : f v ≠ r := fun hcon => hvC ((hmemC v).2 ⟨hvA, hvS, hcon⟩)
    simp only [cut, if_neg hvC]
    exact Finset.mem_erase.2 ⟨hne, hfv⟩
  · have hvA : v ∈ A := Finset.mem_of_mem_erase hv
    have hvr : v ≠ r := (Finset.mem_erase.mp hv).1
    obtain ⟨m, hm⟩ := hf.reaches v hvA
    refine exists_iterate_mem_of_cut' (f := f) (g := cut C f) (C := C) (S := S)
      (S' := S.erase r ∪ C) (r := r) ?_ ?_ ?_ ?_ m v hvr hm
    · intro w hw
      simp [cut, hw]
    · exact Finset.subset_union_right
    · intro w hwS hwr
      exact Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hwr, hwS⟩)
    · intro w hwr hwS hwC hcon
      by_cases hwA : w ∈ A
      · exact hwC ((hmemC w).2 ⟨hwA, hwS, hcon⟩)
      · rw [hf.fixed w (fun hcon2 => hwA (Finset.mem_sdiff.mp hcon2).1)] at hcon
        exact hwr hcon

omit [Fintype V] in
lemma isForest_uncut {A S C : Finset V} {r : V} (hr : r ∈ S) (hSA : S ⊆ A) (hCA : C ⊆ A \ S)
    {g : V → V} (hg : IsForest (A.erase r) (S.erase r ∪ C) g) : IsForest A S (uncut C r g) := by
  refine ⟨?_, ?_, ?_⟩
  · intro v hv
    have hvC : v ∉ C := fun h => hv (hCA h)
    simp [uncut, hvC]
    by_cases hvA : v ∈ A
    · by_cases hvS : v ∈ S
      · have hvnearerase : v ∉ A.erase r \ (S.erase r ∪ C) := by
          simp [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_union]
          tauto
        exact hg.fixed v hvnearerase
      · exfalso; simp_all
    · have hvnearerase : v ∉ A.erase r := fun h => hvA (Finset.mem_of_mem_erase h)
      exact hg.fixed v (by simp_all)
  · intro v hv
    simp at hv
    by_cases hvC : v ∈ C
    · simp [uncut, hvC]; exact hSA hr
    · simp [uncut, hvC]
      have hvne : v ≠ r := fun h => hv.2 (h.symm ▸ hr)
      have hvAerase : v ∈ A.erase r := by simp [hv.1, hvne]
      have hvnotin : v ∉ S.erase r ∪ C := by simp_all [Finset.mem_union]
      exact Finset.mem_of_mem_erase (hg.maps v (Finset.mem_sdiff.mpr ⟨hvAerase, hvnotin⟩))
  · intro v hv
    by_cases hvS : v ∈ S
    · exact ⟨0, hvS⟩
    · -- v ∉ S, so we use exists_iterate_mem_of_cut
      have hvAerase : v ∈ A.erase r := by simp [hv]; intro hvr; exact hvS (hvr ▸ hr)
      obtain ⟨k, hk⟩ := hg.reaches v hvAerase
      -- the `uncut` function agrees with `g` off `C`, and sends `C` to the root `r`
      refine exists_iterate_mem_of_cut (f := uncut C r g) (g := g) (C := C) (S := S)
        (S' := S.erase r ∪ C) (r := r) (fun x hx => by simp [uncut, hx])
        (fun x hx => by simp [uncut, hx]) hr (fun w hw => ?_) k v hk
      rcases Finset.mem_union.mp hw with hw | hw
      · exact Or.inl (Finset.mem_of_mem_erase hw)
      · exact Or.inr hw

omit [Fintype V] in
lemma children_uncut {A S C : Finset V} {r : V} (hr : r ∈ S) (hCA : C ⊆ A \ S) {g : V → V}
    (hg : IsForest (A.erase r) (S.erase r ∪ C) g) : children A S r (uncut C r g) = C := by
  ext v
  simp [children, uncut]
  constructor
  · intro ⟨hvAS, hv⟩
    by_cases hvC : v ∈ C
    · exact hvC
    · simp [hvC] at hv
      -- v ∈ (A.erase r) \ (S.erase r ∪ C) so g v ∈ A.erase r, but g v = r
      have hvr : v ≠ r := fun h => hvAS.2 (h ▸ hr)
      have hv_in : v ∈ (A.erase r) \ (S.erase r ∪ C) := by
        simp [hvAS, hvC, hvr]
      have := hg.maps v hv_in
      simp [hv] at this
  · intro hvC
    have hvAS : v ∈ A ∧ v ∉ S := Finset.mem_sdiff.mp (hCA hvC)
    refine ⟨hvAS, ?_⟩
    simp [hvC]

omit [Fintype V] in
lemma cut_uncut {A S C : Finset V} {r : V} {g : V → V}
    (hg : IsForest (A.erase r) (S.erase r ∪ C) g) : cut C (uncut C r g) = g := by
  ext v
  simp only [cut, uncut]
  split_ifs with hv
  · have hv_root : v ∈ S.erase r ∪ C := Finset.mem_union.mpr (Or.inr hv)
    have : v ∉ (A.erase r) \ (S.erase r ∪ C) := by simp [hv_root]
    exact (hg.fixed v this).symm
  · rfl

omit [Fintype V] in
lemma uncut_cut (A S : Finset V) (r : V) (f : V → V) :
    uncut (children A S r f) r (cut (children A S r f) f) = f := by
  funext v
  simp only [cut, uncut]
  by_cases hv : v ∈ children A S r f <;> simp [hv]
  · exact Eq.symm (Finset.mem_filter.mp hv |>.2)

/-- For a fixed set `C` of children of `r`, cutting is a bijection between the forests on `A`
with roots `S` whose set of children of `r` is `C`, and the forests on `A.erase r` with
roots `S.erase r ∪ C`. -/
lemma card_fiber_eq {A S C : Finset V} {r : V} (hr : r ∈ S) (hSA : S ⊆ A) (hCA : C ⊆ A \ S) :
    ((forestFinset A S).filter (fun f => children A S r f = C)).card
      = (forestFinset (A.erase r) (S.erase r ∪ C)).card := by
  refine Finset.card_nbij' (cut C) (uncut C r) ?_ ?_ ?_ ?_
  · intro f hf
    simp only [Finset.coe_filter, Set.mem_setOf_eq, mem_forestFinset] at hf
    have h := isForest_cut hr hf.1
    rw [hf.2] at h
    simpa using h
  · intro g hg
    simp only [Finset.mem_coe, mem_forestFinset] at hg
    simp only [Finset.coe_filter, Set.mem_setOf_eq, mem_forestFinset]
    exact ⟨isForest_uncut hr hSA hCA hg, children_uncut hr hCA hg⟩
  · intro f hf
    simp only [Finset.coe_filter, Set.mem_setOf_eq, mem_forestFinset] at hf
    have h := uncut_cut A S r f
    rw [hf.2] at h
    exact h
  · intro g hg
    simp only [Finset.mem_coe, mem_forestFinset] at hg
    exact cut_uncut hg

/-- Deleting a root `r` splits the forests on `A` with roots `S` according to the set `C` of
children of `r`. -/
lemma card_forestFinset_split {A S : Finset V} {r : V} (hr : r ∈ S) (hSA : S ⊆ A) :
    (forestFinset A S).card
      = ∑ C ∈ (A \ S).powerset, (forestFinset (A.erase r) (S.erase r ∪ C)).card := by
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun f => children A S r f) (t := (A \ S).powerset)
    (fun f _ => Finset.mem_coe.2 (Finset.mem_powerset.mpr children_subset))]
  exact Finset.sum_congr rfl fun C hC => card_fiber_eq hr hSA (Finset.mem_powerset.mp hC)

end Forest

end Brockian.Cayley
