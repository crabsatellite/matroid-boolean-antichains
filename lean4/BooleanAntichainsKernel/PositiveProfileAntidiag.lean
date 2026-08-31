import BooleanAntichainsKernel.OrderedPartitionInverse
import Mathlib.Algebra.Order.Antidiag.Finsupp

namespace BooleanAntichainsKernel

open scoped Classical

abbrev PositiveFinsuppAntidiag (n b : ℕ) :=
  {l : ℕ →₀ ℕ // l ∈ Finset.finsuppAntidiag (Finset.range b) n ∧
    ∀ i : Fin b, 0 < l i.1}

noncomputable def positiveProfileFinsupp {n b : ℕ} (p : PositiveBlockProfile n b) : ℕ →₀ ℕ :=
  Finsupp.onFinset (Finset.range b)
    (fun k ↦ if h : k < b then p.1 ⟨k, h⟩ else 0)
    (fun k hk ↦ Finset.mem_range.mpr (by
      by_contra h
      simp [h] at hk))

@[simp] theorem positiveProfileFinsupp_fin {n b : ℕ} (p : PositiveBlockProfile n b) (i : Fin b) :
    positiveProfileFinsupp p i.1 = p.1 i := by
  rw [positiveProfileFinsupp, Finsupp.onFinset_apply, dif_pos i.2]

theorem positiveProfileFinsupp_mem {n b : ℕ} (p : PositiveBlockProfile n b) :
    positiveProfileFinsupp p ∈ Finset.finsuppAntidiag (Finset.range b) n := by
  rw [Finset.mem_finsuppAntidiag]
  constructor
  · rw [← Fin.sum_univ_eq_sum_range]
    simpa only [positiveProfileFinsupp_fin] using p.2.1
  · exact Finsupp.support_onFinset_subset

noncomputable def positiveProfileToAntidiag {n b : ℕ} (p : PositiveBlockProfile n b) :
    PositiveFinsuppAntidiag n b :=
  ⟨positiveProfileFinsupp p, positiveProfileFinsupp_mem p,
    fun i ↦ by rw [positiveProfileFinsupp_fin]; exact p.2.2 i⟩

def positiveAntidiagToProfile {n b : ℕ} (l : PositiveFinsuppAntidiag n b) :
    PositiveBlockProfile n b :=
  ⟨fun i ↦ l.1 i.1, by
    have hl := Finset.mem_finsuppAntidiag.mp l.2.1
    rw [Fin.sum_univ_eq_sum_range]
    exact hl.1,
    l.2.2⟩

theorem positiveProfileAntidiag_left {n b : ℕ} (p : PositiveBlockProfile n b) :
    positiveAntidiagToProfile (positiveProfileToAntidiag p) = p := by
  apply Subtype.ext
  funext i
  exact positiveProfileFinsupp_fin p i

theorem positiveProfileAntidiag_right {n b : ℕ} (l : PositiveFinsuppAntidiag n b) :
    positiveProfileToAntidiag (positiveAntidiagToProfile l) = l := by
  apply Subtype.ext
  apply Finsupp.ext
  intro k
  by_cases hk : k < b
  · let i : Fin b := ⟨k, hk⟩
    change positiveProfileFinsupp (positiveAntidiagToProfile l) k = l.1 k
    exact positiveProfileFinsupp_fin _ i
  · have hnot : k ∉ l.1.support := fun hmem ↦
      hk (Finset.mem_range.mp ((Finset.mem_finsuppAntidiag.mp l.2.1).2 hmem))
    have hz : l.1 k = 0 := Finsupp.notMem_support_iff.mp hnot
    change (if h : k < b then (positiveAntidiagToProfile l).1 ⟨k, h⟩ else 0) = l.1 k
    rw [dif_neg hk, hz]

noncomputable def positiveProfileAntidiagEquiv (n b : ℕ) :
    PositiveBlockProfile n b ≃ PositiveFinsuppAntidiag n b where
  toFun := positiveProfileToAntidiag
  invFun := positiveAntidiagToProfile
  left_inv := positiveProfileAntidiag_left
  right_inv := positiveProfileAntidiag_right

noncomputable instance (n b : ℕ) : Fintype (PositiveFinsuppAntidiag n b) :=
  Fintype.ofInjective
    (fun l : PositiveFinsuppAntidiag n b ↦
      (⟨l.1, l.2.1⟩ : {l // l ∈ Finset.finsuppAntidiag (Finset.range b) n}))
    (fun _ _ h ↦ Subtype.ext
      (congrArg (fun z : {l // l ∈ Finset.finsuppAntidiag (Finset.range b) n} ↦ z.1) h))

noncomputable instance (n b : ℕ) : Fintype (PositiveBlockProfile n b) :=
  Fintype.ofEquiv (PositiveFinsuppAntidiag n b) (positiveProfileAntidiagEquiv n b).symm

end BooleanAntichainsKernel
