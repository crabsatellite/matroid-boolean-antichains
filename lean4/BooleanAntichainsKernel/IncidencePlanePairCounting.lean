import BooleanAntichainsKernel.IncidencePlanePairBijection
import Mathlib.Data.Nat.Choose.Basic

namespace BooleanAntichainsKernel

open Finset
open scoped Classical

theorem planeDistinctLines_card (L : Type*) [Fintype L] :
    Fintype.card (PlaneDistinctLines L) = Fintype.card L * (Fintype.card L - 1) := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_subtype_compl, Fintype.card_subtype_eq,
    Finset.sum_const, card_univ, smul_eq_mul]

theorem choose_two_mul_two (n : ℕ) : n.choose 2 * 2 = n * (n - 1) := by
  cases n with
  | zero => simp
  | succ n => simpa using (Nat.add_one_mul_choose_eq n 1).symm

variable {P L : Type*} [Membership P L] [Configuration.ProjectivePlane P L]
variable [Fintype P] [Fintype L]

theorem planeNonincident_at_line_card (l : L) :
    Fintype.card {p : P // p ∉ l} = Configuration.ProjectivePlane.order P L ^ 2 := by
  have hline : Fintype.card {p : P // p ∈ l} = Configuration.ProjectivePlane.order P L + 1 := by
    rw [← Nat.card_eq_fintype_card]
    exact Configuration.ProjectivePlane.pointCount_eq P l
  rw [Fintype.card_subtype_compl (fun p : P ↦ p ∈ l), hline, plane_card_points (L := L)]
  omega

theorem planeNonincidentFlag_card :
    Fintype.card (PlaneNonincidentFlag P L) =
      Fintype.card L * Configuration.ProjectivePlane.order P L ^ 2 := by
  rw [Fintype.card_sigma]
  simp only [planeNonincident_at_line_card, Finset.sum_const, card_univ, smul_eq_mul]

/-- Count the three genuine cases of the proved proper-pair bijection.
The factor two records the two actual point-line orientations. -/
theorem planeProperJoinPair_count :
    Fintype.card (ProperTopJoinPair (L := MatroidFlat (incidencePlaneMatroid P L))) =
      Fintype.card L * (Fintype.card L - 1) +
        2 * (Fintype.card L * Configuration.ProjectivePlane.order P L ^ 2) := by
  rw [← Fintype.card_congr (planeJoinPairEquiv (P := P) (L := L))]
  simp only [Fintype.card_sum, planeDistinctLines_card, planeNonincidentFlag_card]
  omega

/-- Consume the actual ordered/unordered Boolean-antichain fibre, then
cancel the proved factor two and recover the unordered line-pair binomial. -/
theorem incidencePlane_two_count_lines :
    Fintype.card (BooleanAntichain 2 (MatroidFlat (incidencePlaneMatroid P L))) =
      (Fintype.card L).choose 2 + Fintype.card L * Configuration.ProjectivePlane.order P L ^ 2 := by
  have h := Fintype.card_congr
    (properTopJoinPairEquivOrderedBoolean (L := MatroidFlat (incidencePlaneMatroid P L)))
  rw [planeProperJoinPair_count, card_orderedBooleanTuple,
    show (2 : ℕ).factorial = 2 by decide] at h
  have hchoose := choose_two_mul_two (Fintype.card L)
  omega

theorem incidencePlane_two_count :
    Fintype.card (BooleanAntichain 2 (MatroidFlat (incidencePlaneMatroid P L))) =
      (Configuration.ProjectivePlane.order P L ^ 2 + Configuration.ProjectivePlane.order P L + 1).choose 2 +
        (Configuration.ProjectivePlane.order P L ^ 2 + Configuration.ProjectivePlane.order P L + 1) *
          Configuration.ProjectivePlane.order P L ^ 2 := by
  rw [incidencePlane_two_count_lines, plane_card_lines (P := P)]

end BooleanAntichainsKernel
