import BooleanAntichainsKernel.PositiveProfileAntidiag
import BooleanAntichainsKernel.PartitionBellSquareSeries
import Mathlib.RingTheory.PowerSeries.Basic

namespace BooleanAntichainsKernel

open scoped Classical

def positiveAntidiagPredicate (b : ℕ) (l : ℕ →₀ ℕ) : Prop :=
  ∀ i : Fin b, 0 < l i.1

noncomputable def bellSquarePowerTerm (b : ℕ) (l : ℕ →₀ ℕ) : ℚ :=
  ∏ i ∈ Finset.range b, PowerSeries.coeff (l i) bellSquareEGF

theorem bellSquarePowerTerm_zero_of_not_positive {b : ℕ} {l : ℕ →₀ ℕ}
    (h : ¬positiveAntidiagPredicate b l) :
    bellSquarePowerTerm b l = 0 := by
  obtain ⟨i, hi⟩ := Classical.not_forall.mp h
  have hz : l i.1 = 0 := Nat.eq_zero_of_not_pos hi
  apply Finset.prod_eq_zero (Finset.mem_range.mpr i.2)
  rw [hz, bellSquareEGF_coeff]
  rfl

theorem bellSquarePower_sum_filter (n b : ℕ) :
    (∑ l ∈ Finset.finsuppAntidiag (Finset.range b) n, bellSquarePowerTerm b l) =
      ∑ l ∈ (Finset.finsuppAntidiag (Finset.range b) n).filter
        (positiveAntidiagPredicate b), bellSquarePowerTerm b l := by
  apply (Finset.sum_subset (Finset.filter_subset _ _)
    (fun l hl hnot ↦ bellSquarePowerTerm_zero_of_not_positive
      (fun hp ↦ hnot (Finset.mem_filter.mpr ⟨hl, hp⟩)))).symm

theorem bellSquarePower_positiveAntidiag_sum (n b : ℕ) :
    (∑ l ∈ Finset.finsuppAntidiag (Finset.range b) n, bellSquarePowerTerm b l) =
      ∑ l : PositiveFinsuppAntidiag n b, bellSquarePowerTerm b l.1 := by
  rw [bellSquarePower_sum_filter]
  exact Finset.sum_subtype
    ((Finset.finsuppAntidiag (Finset.range b) n).filter (positiveAntidiagPredicate b))
    (fun l ↦ by simp [positiveAntidiagPredicate])
    (bellSquarePowerTerm b)

def positiveProfilePowerTerm {n b : ℕ} (p : PositiveBlockProfile n b) : ℚ :=
  ∏ i : Fin b, (Nat.bell (p.1 i) : ℚ) ^ 2 / (p.1 i).factorial

theorem bellSquarePowerTerm_profile {n b : ℕ} (p : PositiveBlockProfile n b) :
    bellSquarePowerTerm b (positiveProfileFinsupp p) = positiveProfilePowerTerm p := by
  rw [bellSquarePowerTerm, ← Fin.prod_univ_eq_prod_range]
  apply Finset.prod_congr rfl
  intro i _hi
  rw [positiveProfileFinsupp_fin, bellSquareEGF_coeff]
  simp only [bellSquareEGFCoeff, if_neg (Nat.ne_of_gt (p.2.2 i))]

/-- Exact positive-profile expansion of the power coefficient. -/
theorem bellSquareEGF_coeff_pow_profiles (n b : ℕ) :
    PowerSeries.coeff n (bellSquareEGF ^ b) =
      ∑ p : PositiveBlockProfile n b, positiveProfilePowerTerm p := by
  rw [PowerSeries.coeff_pow]
  change (∑ l ∈ Finset.finsuppAntidiag (Finset.range b) n,
    bellSquarePowerTerm b l) = _
  rw [bellSquarePower_positiveAntidiag_sum]
  have h := (positiveProfileAntidiagEquiv n b).sum_comp
    (fun l : PositiveFinsuppAntidiag n b ↦ bellSquarePowerTerm b l.1)
  calc
    _ = ∑ p : PositiveBlockProfile n b,
        bellSquarePowerTerm b (positiveProfileFinsupp p) := h.symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p _hp
      exact bellSquarePowerTerm_profile p

end BooleanAntichainsKernel
