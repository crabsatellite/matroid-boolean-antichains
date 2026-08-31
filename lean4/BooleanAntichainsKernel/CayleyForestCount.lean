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
import BooleanAntichainsKernel.CayleyForestCut
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.Ring

namespace Brockian.Cayley

open Finset

section Forest

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! #### The binomial identity -/

lemma sum_choose_pow (m q : ℕ) :
    ∑ i ∈ Finset.range (m + 1), m.choose i * q ^ (m - i) = (q + 1) ^ m := by
  rw [add_pow, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun i hi => ?_
  simp only [Finset.mem_range] at hi
  have h1 : m + 1 - 1 - i = m - i := by omega
  have h2 : m - (m - i) = i := by omega
  rw [h1, h2, Nat.choose_symm (by omega)]
  simp [mul_comm]

lemma sum_choose_mul_pow (m q : ℕ) :
    ∑ i ∈ Finset.range (m + 1), m.choose i * (i * q ^ (m - i)) = m * (q + 1) ^ (m - 1) := by
  cases m with
  | zero => simp
  | succ k =>
    rw [Finset.sum_range_succ']
    simp only [zero_mul, mul_zero, add_zero, Nat.add_sub_cancel, ← sum_choose_pow k q,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun t ht => ?_
    have h1 : k + 1 - (t + 1) = k - t := by omega
    rw [h1]
    calc (k + 1).choose (t + 1) * ((t + 1) * q ^ (k - t))
        = ((k + 1).choose (t + 1) * (t + 1)) * q ^ (k - t) := by ring
      _ = ((k + 1) * k.choose t) * q ^ (k - t) := by rw [← Nat.add_one_mul_choose_eq]
      _ = (k + 1) * (k.choose t * q ^ (k - t)) := by ring

lemma sum_aux (j m q : ℕ) :
    ∑ i ∈ Finset.range (m + 1), m.choose i * ((j + i) * q ^ (m - i))
      = j * (q + 1) ^ m + m * (q + 1) ^ (m - 1) := by
  have h : ∀ i, m.choose i * ((j + i) * q ^ (m - i))
      = j * (m.choose i * q ^ (m - i)) + m.choose i * (i * q ^ (m - i)) := by
    intro i; ring
  simp_rw [h]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, sum_choose_pow, sum_choose_mul_pow]

lemma sum_binom_aux (j m : ℕ) :
    (j + 1 + m) * ∑ i ∈ Finset.range (m + 1), m.choose i * ((j + i) * (j + m) ^ (m - i))
      = (j + 1) * ((j + m) * (j + 1 + m) ^ m) := by
  rw [sum_aux, show j + m + 1 = j + 1 + m from by ring]
  cases m with
  | zero => simp
  | succ k =>
    rw [show k + 1 - 1 = k from rfl, pow_succ]
    ring

lemma card_forestFinset_aux : ∀ (n : ℕ) (A S : Finset V), A.card = n → S ⊆ A →
    A.card * (forestFinset A S).card = S.card * A.card ^ (A.card - S.card) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro A S hA hSA
  rcases S.eq_empty_or_nonempty with rfl | hS
  · rcases A.eq_empty_or_nonempty with rfl | hA'
    · simp
    · rw [forestFinset_empty_roots hA']
      simp
  · by_cases hAS : S = A
    · subst hAS
      rw [forestFinset_self]
      simp
    · obtain ⟨r, hr⟩ := hS
      have hrA : r ∈ A := hSA hr
      have hlt : S.card < A.card := Finset.card_lt_card (lt_of_le_of_ne hSA hAS)
      obtain ⟨j, hj⟩ : ∃ j, S.card = j + 1 :=
        ⟨S.card - 1, by have := Finset.card_pos.mpr ⟨r, hr⟩; omega⟩
      set m := (A \ S).card with hm
      have hmA : A.card = j + 1 + m := by
        have := Finset.card_sdiff_add_card_eq_card hSA
        omega
      have hm1 : 1 ≤ m := by omega
      have hAe : (A.erase r).card = j + m := by
        rw [Finset.card_erase_of_mem hrA, hmA]; omega
      have key : (j + m) * (forestFinset A S).card
          = ∑ C ∈ (A \ S).powerset, ((j + C.card) * (j + m) ^ (m - C.card)) := by
        rw [card_forestFinset_split hr hSA, Finset.mul_sum]
        refine Finset.sum_congr rfl fun C hC => ?_
        have hCA : C ⊆ A \ S := Finset.mem_powerset.mp hC
        have hCcard : C.card ≤ m := hm ▸ Finset.card_le_card hCA
        have hdisj : Disjoint (S.erase r) C := by
          refine Finset.disjoint_left.2 fun a ha haC => ?_
          exact (Finset.mem_sdiff.mp (hCA haC)).2 (Finset.mem_of_mem_erase ha)
        have hsub : S.erase r ∪ C ⊆ A.erase r := by
          refine Finset.union_subset (Finset.erase_subset_erase _ hSA) fun a ha => ?_
          have ha' := Finset.mem_sdiff.mp (hCA ha)
          exact Finset.mem_erase.2 ⟨fun h => ha'.2 (h ▸ hr), ha'.1⟩
        have hcards : (S.erase r ∪ C).card = j + C.card := by
          rw [Finset.card_union_of_disjoint hdisj, Finset.card_erase_of_mem hr, hj]
          omega
        have h := ih (A.erase r).card (by omega) (A.erase r) (S.erase r ∪ C) rfl hsub
        rw [hAe, hcards] at h
        rw [h]
        congr 2
        omega
      rw [Finset.sum_powerset_apply_card (fun i => (j + i) * (j + m) ^ (m - i))] at key
      simp only [Nat.nsmul_eq_mul, ← hm] at key
      have main := sum_binom_aux j m
      rw [← key] at main
      have h2 : (j + m) * ((j + 1 + m) * (forestFinset A S).card)
          = (j + m) * ((j + 1) * (j + 1 + m) ^ m) := by
        calc (j + m) * ((j + 1 + m) * (forestFinset A S).card)
            = (j + 1 + m) * ((j + m) * (forestFinset A S).card) := by ring
          _ = (j + 1) * ((j + m) * (j + 1 + m) ^ m) := main
          _ = (j + m) * ((j + 1) * (j + 1 + m) ^ m) := by ring
      have h3 := Nat.eq_of_mul_eq_mul_left (by omega : 0 < j + m) h2
      rw [hmA, hj, show j + 1 + m - (j + 1) = m by omega]
      exact h3

/-- **The number of rooted forests.** -/
theorem card_forestFinset (A S : Finset V) (hSA : S ⊆ A) :
    A.card * (forestFinset A S).card = S.card * A.card ^ (A.card - S.card) :=
  card_forestFinset_aux A.card A S rfl hSA

end Forest

end Brockian.Cayley
