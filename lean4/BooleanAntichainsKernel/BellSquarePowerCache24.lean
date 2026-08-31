import BooleanAntichainsKernel.BellSquareCoefficientRecurrence
import BooleanAntichainsKernel.PartitionBellSmall

namespace BooleanAntichainsKernel

theorem bellPower_one (n : ℕ) :
    bellSquarePowerCoeffRec 1 n = bellSquareEGFCoeff n := by
  rw [← bellSquareEGF_coeff_pow_rec]
  simp [bellSquareEGF_coeff]

theorem bellPower_two_0 :
    bellSquarePowerCoeffRec 2 0 = (0 : ℚ) := by
  rw [show 2 = 1 + 1 by omega, bellSquarePowerCoeffRec_succ,
    Finset.Nat.antidiagonal_eq_map]
  norm_num [Finset.sum_range_succ, bellPower_one,
    bellSquareEGFCoeff, Nat.factorial, Nat.bell, partitionBell_three, partitionBell_four, partitionBell_five,
      partitionBell_six, partitionBell_seven]

theorem bellPower_two_1 :
    bellSquarePowerCoeffRec 2 1 = (0 : ℚ) := by
  rw [show 2 = 1 + 1 by omega, bellSquarePowerCoeffRec_succ,
    Finset.Nat.antidiagonal_eq_map]
  norm_num [Finset.sum_range_succ, bellPower_one,
    bellSquareEGFCoeff, Nat.factorial, Nat.bell, partitionBell_three, partitionBell_four, partitionBell_five,
      partitionBell_six, partitionBell_seven]

theorem bellPower_two_2 :
    bellSquarePowerCoeffRec 2 2 = (1 : ℚ) := by
  rw [show 2 = 1 + 1 by omega, bellSquarePowerCoeffRec_succ,
    Finset.Nat.antidiagonal_eq_map]
  norm_num [Finset.sum_range_succ, bellPower_one,
    bellSquareEGFCoeff, Nat.factorial, Nat.bell, partitionBell_three, partitionBell_four, partitionBell_five,
      partitionBell_six, partitionBell_seven]

theorem bellPower_two_3 :
    bellSquarePowerCoeffRec 2 3 = (4 : ℚ) := by
  rw [show 2 = 1 + 1 by omega, bellSquarePowerCoeffRec_succ,
    Finset.Nat.antidiagonal_eq_map]
  norm_num [Finset.sum_range_succ, bellPower_one,
    bellSquareEGFCoeff, Nat.factorial, Nat.bell, partitionBell_three, partitionBell_four, partitionBell_five,
      partitionBell_six, partitionBell_seven]

theorem bellPower_two_4 :
    bellSquarePowerCoeffRec 2 4 = (37 : ℚ) / 3 := by
  rw [show 2 = 1 + 1 by omega, bellSquarePowerCoeffRec_succ,
    Finset.Nat.antidiagonal_eq_map]
  norm_num [Finset.sum_range_succ, bellPower_one,
    bellSquareEGFCoeff, Nat.factorial, Nat.bell, partitionBell_three, partitionBell_four, partitionBell_five,
      partitionBell_six, partitionBell_seven]

theorem bellPower_two_5 :
    bellSquarePowerCoeffRec 2 5 = (425 : ℚ) / 12 := by
  rw [show 2 = 1 + 1 by omega, bellSquarePowerCoeffRec_succ,
    Finset.Nat.antidiagonal_eq_map]
  norm_num [Finset.sum_range_succ, bellPower_one,
    bellSquareEGFCoeff, Nat.factorial, Nat.bell, partitionBell_three, partitionBell_four, partitionBell_five,
      partitionBell_six, partitionBell_seven]

theorem bellPower_two_6 :
    bellSquarePowerCoeffRec 2 6 = (17987 : ℚ) / 180 := by
  rw [show 2 = 1 + 1 by omega, bellSquarePowerCoeffRec_succ,
    Finset.Nat.antidiagonal_eq_map]
  norm_num [Finset.sum_range_succ, bellPower_one,
    bellSquareEGFCoeff, Nat.factorial, Nat.bell, partitionBell_three, partitionBell_four, partitionBell_five,
      partitionBell_six, partitionBell_seven]

theorem bellPower_two_7 :
    bellSquarePowerCoeffRec 2 7 = (50891 : ℚ) / 180 := by
  rw [show 2 = 1 + 1 by omega, bellSquarePowerCoeffRec_succ,
    Finset.Nat.antidiagonal_eq_map]
  norm_num [Finset.sum_range_succ, bellPower_one,
    bellSquareEGFCoeff, Nat.factorial, Nat.bell, partitionBell_three, partitionBell_four, partitionBell_five,
      partitionBell_six, partitionBell_seven]

theorem bellPower_three_0 :
    bellSquarePowerCoeffRec 3 0 = (0 : ℚ) := by
  rw [show 3 = 2 + 1 by omega, bellSquarePowerCoeffRec_succ,
    Finset.Nat.antidiagonal_eq_map]
  norm_num [Finset.sum_range_succ, bellPower_two_0, bellPower_two_1, bellPower_two_2, bellPower_two_3, bellPower_two_4, bellPower_two_5, bellPower_two_6, bellPower_two_7,
    bellSquareEGFCoeff, Nat.factorial, Nat.bell, partitionBell_three, partitionBell_four, partitionBell_five,
      partitionBell_six, partitionBell_seven]

theorem bellPower_three_1 :
    bellSquarePowerCoeffRec 3 1 = (0 : ℚ) := by
  rw [show 3 = 2 + 1 by omega, bellSquarePowerCoeffRec_succ,
    Finset.Nat.antidiagonal_eq_map]
  norm_num [Finset.sum_range_succ, bellPower_two_0, bellPower_two_1, bellPower_two_2, bellPower_two_3, bellPower_two_4, bellPower_two_5, bellPower_two_6, bellPower_two_7,
    bellSquareEGFCoeff, Nat.factorial, Nat.bell, partitionBell_three, partitionBell_four, partitionBell_five,
      partitionBell_six, partitionBell_seven]

theorem bellPower_three_2 :
    bellSquarePowerCoeffRec 3 2 = (0 : ℚ) := by
  rw [show 3 = 2 + 1 by omega, bellSquarePowerCoeffRec_succ,
    Finset.Nat.antidiagonal_eq_map]
  norm_num [Finset.sum_range_succ, bellPower_two_0, bellPower_two_1, bellPower_two_2, bellPower_two_3, bellPower_two_4, bellPower_two_5, bellPower_two_6, bellPower_two_7,
    bellSquareEGFCoeff, Nat.factorial, Nat.bell, partitionBell_three, partitionBell_four, partitionBell_five,
      partitionBell_six, partitionBell_seven]

theorem bellPower_three_3 :
    bellSquarePowerCoeffRec 3 3 = (1 : ℚ) := by
  rw [show 3 = 2 + 1 by omega, bellSquarePowerCoeffRec_succ,
    Finset.Nat.antidiagonal_eq_map]
  norm_num [Finset.sum_range_succ, bellPower_two_0, bellPower_two_1, bellPower_two_2, bellPower_two_3, bellPower_two_4, bellPower_two_5, bellPower_two_6, bellPower_two_7,
    bellSquareEGFCoeff, Nat.factorial, Nat.bell, partitionBell_three, partitionBell_four, partitionBell_five,
      partitionBell_six, partitionBell_seven]

theorem bellPower_three_4 :
    bellSquarePowerCoeffRec 3 4 = (6 : ℚ) := by
  rw [show 3 = 2 + 1 by omega, bellSquarePowerCoeffRec_succ,
    Finset.Nat.antidiagonal_eq_map]
  norm_num [Finset.sum_range_succ, bellPower_two_0, bellPower_two_1, bellPower_two_2, bellPower_two_3, bellPower_two_4, bellPower_two_5, bellPower_two_6, bellPower_two_7,
    bellSquareEGFCoeff, Nat.factorial, Nat.bell, partitionBell_three, partitionBell_four, partitionBell_five,
      partitionBell_six, partitionBell_seven]

theorem bellPower_three_5 :
    bellSquarePowerCoeffRec 3 5 = (49 : ℚ) / 2 := by
  rw [show 3 = 2 + 1 by omega, bellSquarePowerCoeffRec_succ,
    Finset.Nat.antidiagonal_eq_map]
  norm_num [Finset.sum_range_succ, bellPower_two_0, bellPower_two_1, bellPower_two_2, bellPower_two_3, bellPower_two_4, bellPower_two_5, bellPower_two_6, bellPower_two_7,
    bellSquareEGFCoeff, Nat.factorial, Nat.bell, partitionBell_three, partitionBell_four, partitionBell_five,
      partitionBell_six, partitionBell_seven]

theorem bellPower_three_6 :
    bellSquarePowerCoeffRec 3 6 = (689 : ℚ) / 8 := by
  rw [show 3 = 2 + 1 by omega, bellSquarePowerCoeffRec_succ,
    Finset.Nat.antidiagonal_eq_map]
  norm_num [Finset.sum_range_succ, bellPower_two_0, bellPower_two_1, bellPower_two_2, bellPower_two_3, bellPower_two_4, bellPower_two_5, bellPower_two_6, bellPower_two_7,
    bellSquareEGFCoeff, Nat.factorial, Nat.bell, partitionBell_three, partitionBell_four, partitionBell_five,
      partitionBell_six, partitionBell_seven]

theorem bellPower_three_7 :
    bellSquarePowerCoeffRec 3 7 = (16931 : ℚ) / 60 := by
  rw [show 3 = 2 + 1 by omega, bellSquarePowerCoeffRec_succ,
    Finset.Nat.antidiagonal_eq_map]
  norm_num [Finset.sum_range_succ, bellPower_two_0, bellPower_two_1, bellPower_two_2, bellPower_two_3, bellPower_two_4, bellPower_two_5, bellPower_two_6, bellPower_two_7,
    bellSquareEGFCoeff, Nat.factorial, Nat.bell, partitionBell_three, partitionBell_four, partitionBell_five,
      partitionBell_six, partitionBell_seven]

theorem bellPower_four_0 :
    bellSquarePowerCoeffRec 4 0 = (0 : ℚ) := by
  rw [show 4 = 3 + 1 by omega, bellSquarePowerCoeffRec_succ,
    Finset.Nat.antidiagonal_eq_map]
  norm_num [Finset.sum_range_succ, bellPower_three_0, bellPower_three_1, bellPower_three_2, bellPower_three_3, bellPower_three_4, bellPower_three_5, bellPower_three_6, bellPower_three_7,
    bellSquareEGFCoeff, Nat.factorial, Nat.bell, partitionBell_three, partitionBell_four, partitionBell_five,
      partitionBell_six, partitionBell_seven]

theorem bellPower_four_1 :
    bellSquarePowerCoeffRec 4 1 = (0 : ℚ) := by
  rw [show 4 = 3 + 1 by omega, bellSquarePowerCoeffRec_succ,
    Finset.Nat.antidiagonal_eq_map]
  norm_num [Finset.sum_range_succ, bellPower_three_0, bellPower_three_1, bellPower_three_2, bellPower_three_3, bellPower_three_4, bellPower_three_5, bellPower_three_6, bellPower_three_7,
    bellSquareEGFCoeff, Nat.factorial, Nat.bell, partitionBell_three, partitionBell_four, partitionBell_five,
      partitionBell_six, partitionBell_seven]

theorem bellPower_four_2 :
    bellSquarePowerCoeffRec 4 2 = (0 : ℚ) := by
  rw [show 4 = 3 + 1 by omega, bellSquarePowerCoeffRec_succ,
    Finset.Nat.antidiagonal_eq_map]
  norm_num [Finset.sum_range_succ, bellPower_three_0, bellPower_three_1, bellPower_three_2, bellPower_three_3, bellPower_three_4, bellPower_three_5, bellPower_three_6, bellPower_three_7,
    bellSquareEGFCoeff, Nat.factorial, Nat.bell, partitionBell_three, partitionBell_four, partitionBell_five,
      partitionBell_six, partitionBell_seven]

theorem bellPower_four_3 :
    bellSquarePowerCoeffRec 4 3 = (0 : ℚ) := by
  rw [show 4 = 3 + 1 by omega, bellSquarePowerCoeffRec_succ,
    Finset.Nat.antidiagonal_eq_map]
  norm_num [Finset.sum_range_succ, bellPower_three_0, bellPower_three_1, bellPower_three_2, bellPower_three_3, bellPower_three_4, bellPower_three_5, bellPower_three_6, bellPower_three_7,
    bellSquareEGFCoeff, Nat.factorial, Nat.bell, partitionBell_three, partitionBell_four, partitionBell_five,
      partitionBell_six, partitionBell_seven]

theorem bellPower_four_4 :
    bellSquarePowerCoeffRec 4 4 = (1 : ℚ) := by
  rw [show 4 = 3 + 1 by omega, bellSquarePowerCoeffRec_succ,
    Finset.Nat.antidiagonal_eq_map]
  norm_num [Finset.sum_range_succ, bellPower_three_0, bellPower_three_1, bellPower_three_2, bellPower_three_3, bellPower_three_4, bellPower_three_5, bellPower_three_6, bellPower_three_7,
    bellSquareEGFCoeff, Nat.factorial, Nat.bell, partitionBell_three, partitionBell_four, partitionBell_five,
      partitionBell_six, partitionBell_seven]

theorem bellPower_four_5 :
    bellSquarePowerCoeffRec 4 5 = (8 : ℚ) := by
  rw [show 4 = 3 + 1 by omega, bellSquarePowerCoeffRec_succ,
    Finset.Nat.antidiagonal_eq_map]
  norm_num [Finset.sum_range_succ, bellPower_three_0, bellPower_three_1, bellPower_three_2, bellPower_three_3, bellPower_three_4, bellPower_three_5, bellPower_three_6, bellPower_three_7,
    bellSquareEGFCoeff, Nat.factorial, Nat.bell, partitionBell_three, partitionBell_four, partitionBell_five,
      partitionBell_six, partitionBell_seven]

theorem bellPower_four_6 :
    bellSquarePowerCoeffRec 4 6 = (122 : ℚ) / 3 := by
  rw [show 4 = 3 + 1 by omega, bellSquarePowerCoeffRec_succ,
    Finset.Nat.antidiagonal_eq_map]
  norm_num [Finset.sum_range_succ, bellPower_three_0, bellPower_three_1, bellPower_three_2, bellPower_three_3, bellPower_three_4, bellPower_three_5, bellPower_three_6, bellPower_three_7,
    bellSquareEGFCoeff, Nat.factorial, Nat.bell, partitionBell_three, partitionBell_four, partitionBell_five,
      partitionBell_six, partitionBell_seven]

theorem bellPower_four_7 :
    bellSquarePowerCoeffRec 4 7 = (339 : ℚ) / 2 := by
  rw [show 4 = 3 + 1 by omega, bellSquarePowerCoeffRec_succ,
    Finset.Nat.antidiagonal_eq_map]
  norm_num [Finset.sum_range_succ, bellPower_three_0, bellPower_three_1, bellPower_three_2, bellPower_three_3, bellPower_three_4, bellPower_three_5, bellPower_three_6, bellPower_three_7,
    bellSquareEGFCoeff, Nat.factorial, Nat.bell, partitionBell_three, partitionBell_four, partitionBell_five,
      partitionBell_six, partitionBell_seven]

end BooleanAntichainsKernel
