import BooleanAntichainsKernel.BellSquarePowerCache24

namespace BooleanAntichainsKernel

theorem bellPower_five_0 :
    bellSquarePowerCoeffRec 5 0 = (0 : ℚ) := by
  rw [show 5 = 4 + 1 by omega, bellSquarePowerCoeffRec_succ,
    Finset.Nat.antidiagonal_eq_map]
  norm_num [Finset.sum_range_succ, bellPower_four_0, bellPower_four_1, bellPower_four_2, bellPower_four_3, bellPower_four_4, bellPower_four_5, bellPower_four_6, bellPower_four_7,
    bellSquareEGFCoeff, Nat.factorial, Nat.bell, partitionBell_three,
    partitionBell_four, partitionBell_five, partitionBell_six, partitionBell_seven]

theorem bellPower_five_1 :
    bellSquarePowerCoeffRec 5 1 = (0 : ℚ) := by
  rw [show 5 = 4 + 1 by omega, bellSquarePowerCoeffRec_succ,
    Finset.Nat.antidiagonal_eq_map]
  norm_num [Finset.sum_range_succ, bellPower_four_0, bellPower_four_1, bellPower_four_2, bellPower_four_3, bellPower_four_4, bellPower_four_5, bellPower_four_6, bellPower_four_7,
    bellSquareEGFCoeff, Nat.factorial, Nat.bell, partitionBell_three,
    partitionBell_four, partitionBell_five, partitionBell_six, partitionBell_seven]

theorem bellPower_five_2 :
    bellSquarePowerCoeffRec 5 2 = (0 : ℚ) := by
  rw [show 5 = 4 + 1 by omega, bellSquarePowerCoeffRec_succ,
    Finset.Nat.antidiagonal_eq_map]
  norm_num [Finset.sum_range_succ, bellPower_four_0, bellPower_four_1, bellPower_four_2, bellPower_four_3, bellPower_four_4, bellPower_four_5, bellPower_four_6, bellPower_four_7,
    bellSquareEGFCoeff, Nat.factorial, Nat.bell, partitionBell_three,
    partitionBell_four, partitionBell_five, partitionBell_six, partitionBell_seven]

theorem bellPower_five_3 :
    bellSquarePowerCoeffRec 5 3 = (0 : ℚ) := by
  rw [show 5 = 4 + 1 by omega, bellSquarePowerCoeffRec_succ,
    Finset.Nat.antidiagonal_eq_map]
  norm_num [Finset.sum_range_succ, bellPower_four_0, bellPower_four_1, bellPower_four_2, bellPower_four_3, bellPower_four_4, bellPower_four_5, bellPower_four_6, bellPower_four_7,
    bellSquareEGFCoeff, Nat.factorial, Nat.bell, partitionBell_three,
    partitionBell_four, partitionBell_five, partitionBell_six, partitionBell_seven]

theorem bellPower_five_4 :
    bellSquarePowerCoeffRec 5 4 = (0 : ℚ) := by
  rw [show 5 = 4 + 1 by omega, bellSquarePowerCoeffRec_succ,
    Finset.Nat.antidiagonal_eq_map]
  norm_num [Finset.sum_range_succ, bellPower_four_0, bellPower_four_1, bellPower_four_2, bellPower_four_3, bellPower_four_4, bellPower_four_5, bellPower_four_6, bellPower_four_7,
    bellSquareEGFCoeff, Nat.factorial, Nat.bell, partitionBell_three,
    partitionBell_four, partitionBell_five, partitionBell_six, partitionBell_seven]

theorem bellPower_five_5 :
    bellSquarePowerCoeffRec 5 5 = (1 : ℚ) := by
  rw [show 5 = 4 + 1 by omega, bellSquarePowerCoeffRec_succ,
    Finset.Nat.antidiagonal_eq_map]
  norm_num [Finset.sum_range_succ, bellPower_four_0, bellPower_four_1, bellPower_four_2, bellPower_four_3, bellPower_four_4, bellPower_four_5, bellPower_four_6, bellPower_four_7,
    bellSquareEGFCoeff, Nat.factorial, Nat.bell, partitionBell_three,
    partitionBell_four, partitionBell_five, partitionBell_six, partitionBell_seven]

theorem bellPower_five_6 :
    bellSquarePowerCoeffRec 5 6 = (10 : ℚ) := by
  rw [show 5 = 4 + 1 by omega, bellSquarePowerCoeffRec_succ,
    Finset.Nat.antidiagonal_eq_map]
  norm_num [Finset.sum_range_succ, bellPower_four_0, bellPower_four_1, bellPower_four_2, bellPower_four_3, bellPower_four_4, bellPower_four_5, bellPower_four_6, bellPower_four_7,
    bellSquareEGFCoeff, Nat.factorial, Nat.bell, partitionBell_three,
    partitionBell_four, partitionBell_five, partitionBell_six, partitionBell_seven]

theorem bellPower_five_7 :
    bellSquarePowerCoeffRec 5 7 = (365 : ℚ) / 6 := by
  rw [show 5 = 4 + 1 by omega, bellSquarePowerCoeffRec_succ,
    Finset.Nat.antidiagonal_eq_map]
  norm_num [Finset.sum_range_succ, bellPower_four_0, bellPower_four_1, bellPower_four_2, bellPower_four_3, bellPower_four_4, bellPower_four_5, bellPower_four_6, bellPower_four_7,
    bellSquareEGFCoeff, Nat.factorial, Nat.bell, partitionBell_three,
    partitionBell_four, partitionBell_five, partitionBell_six, partitionBell_seven]

theorem bellPower_six_0 :
    bellSquarePowerCoeffRec 6 0 = (0 : ℚ) := by
  rw [show 6 = 5 + 1 by omega, bellSquarePowerCoeffRec_succ,
    Finset.Nat.antidiagonal_eq_map]
  norm_num [Finset.sum_range_succ, bellPower_five_0, bellPower_five_1, bellPower_five_2, bellPower_five_3, bellPower_five_4, bellPower_five_5, bellPower_five_6, bellPower_five_7,
    bellSquareEGFCoeff, Nat.factorial, Nat.bell, partitionBell_three,
    partitionBell_four, partitionBell_five, partitionBell_six, partitionBell_seven]

theorem bellPower_six_1 :
    bellSquarePowerCoeffRec 6 1 = (0 : ℚ) := by
  rw [show 6 = 5 + 1 by omega, bellSquarePowerCoeffRec_succ,
    Finset.Nat.antidiagonal_eq_map]
  norm_num [Finset.sum_range_succ, bellPower_five_0, bellPower_five_1, bellPower_five_2, bellPower_five_3, bellPower_five_4, bellPower_five_5, bellPower_five_6, bellPower_five_7,
    bellSquareEGFCoeff, Nat.factorial, Nat.bell, partitionBell_three,
    partitionBell_four, partitionBell_five, partitionBell_six, partitionBell_seven]

theorem bellPower_six_2 :
    bellSquarePowerCoeffRec 6 2 = (0 : ℚ) := by
  rw [show 6 = 5 + 1 by omega, bellSquarePowerCoeffRec_succ,
    Finset.Nat.antidiagonal_eq_map]
  norm_num [Finset.sum_range_succ, bellPower_five_0, bellPower_five_1, bellPower_five_2, bellPower_five_3, bellPower_five_4, bellPower_five_5, bellPower_five_6, bellPower_five_7,
    bellSquareEGFCoeff, Nat.factorial, Nat.bell, partitionBell_three,
    partitionBell_four, partitionBell_five, partitionBell_six, partitionBell_seven]

theorem bellPower_six_3 :
    bellSquarePowerCoeffRec 6 3 = (0 : ℚ) := by
  rw [show 6 = 5 + 1 by omega, bellSquarePowerCoeffRec_succ,
    Finset.Nat.antidiagonal_eq_map]
  norm_num [Finset.sum_range_succ, bellPower_five_0, bellPower_five_1, bellPower_five_2, bellPower_five_3, bellPower_five_4, bellPower_five_5, bellPower_five_6, bellPower_five_7,
    bellSquareEGFCoeff, Nat.factorial, Nat.bell, partitionBell_three,
    partitionBell_four, partitionBell_five, partitionBell_six, partitionBell_seven]

theorem bellPower_six_4 :
    bellSquarePowerCoeffRec 6 4 = (0 : ℚ) := by
  rw [show 6 = 5 + 1 by omega, bellSquarePowerCoeffRec_succ,
    Finset.Nat.antidiagonal_eq_map]
  norm_num [Finset.sum_range_succ, bellPower_five_0, bellPower_five_1, bellPower_five_2, bellPower_five_3, bellPower_five_4, bellPower_five_5, bellPower_five_6, bellPower_five_7,
    bellSquareEGFCoeff, Nat.factorial, Nat.bell, partitionBell_three,
    partitionBell_four, partitionBell_five, partitionBell_six, partitionBell_seven]

theorem bellPower_six_5 :
    bellSquarePowerCoeffRec 6 5 = (0 : ℚ) := by
  rw [show 6 = 5 + 1 by omega, bellSquarePowerCoeffRec_succ,
    Finset.Nat.antidiagonal_eq_map]
  norm_num [Finset.sum_range_succ, bellPower_five_0, bellPower_five_1, bellPower_five_2, bellPower_five_3, bellPower_five_4, bellPower_five_5, bellPower_five_6, bellPower_five_7,
    bellSquareEGFCoeff, Nat.factorial, Nat.bell, partitionBell_three,
    partitionBell_four, partitionBell_five, partitionBell_six, partitionBell_seven]

theorem bellPower_six_6 :
    bellSquarePowerCoeffRec 6 6 = (1 : ℚ) := by
  rw [show 6 = 5 + 1 by omega, bellSquarePowerCoeffRec_succ,
    Finset.Nat.antidiagonal_eq_map]
  norm_num [Finset.sum_range_succ, bellPower_five_0, bellPower_five_1, bellPower_five_2, bellPower_five_3, bellPower_five_4, bellPower_five_5, bellPower_five_6, bellPower_five_7,
    bellSquareEGFCoeff, Nat.factorial, Nat.bell, partitionBell_three,
    partitionBell_four, partitionBell_five, partitionBell_six, partitionBell_seven]

theorem bellPower_six_7 :
    bellSquarePowerCoeffRec 6 7 = (12 : ℚ) := by
  rw [show 6 = 5 + 1 by omega, bellSquarePowerCoeffRec_succ,
    Finset.Nat.antidiagonal_eq_map]
  norm_num [Finset.sum_range_succ, bellPower_five_0, bellPower_five_1, bellPower_five_2, bellPower_five_3, bellPower_five_4, bellPower_five_5, bellPower_five_6, bellPower_five_7,
    bellSquareEGFCoeff, Nat.factorial, Nat.bell, partitionBell_three,
    partitionBell_four, partitionBell_five, partitionBell_six, partitionBell_seven]

theorem bellPower_seven_0 :
    bellSquarePowerCoeffRec 7 0 = (0 : ℚ) := by
  rw [show 7 = 6 + 1 by omega, bellSquarePowerCoeffRec_succ,
    Finset.Nat.antidiagonal_eq_map]
  norm_num [Finset.sum_range_succ, bellPower_six_0, bellPower_six_1, bellPower_six_2, bellPower_six_3, bellPower_six_4, bellPower_six_5, bellPower_six_6, bellPower_six_7,
    bellSquareEGFCoeff, Nat.factorial, Nat.bell, partitionBell_three,
    partitionBell_four, partitionBell_five, partitionBell_six, partitionBell_seven]

theorem bellPower_seven_1 :
    bellSquarePowerCoeffRec 7 1 = (0 : ℚ) := by
  rw [show 7 = 6 + 1 by omega, bellSquarePowerCoeffRec_succ,
    Finset.Nat.antidiagonal_eq_map]
  norm_num [Finset.sum_range_succ, bellPower_six_0, bellPower_six_1, bellPower_six_2, bellPower_six_3, bellPower_six_4, bellPower_six_5, bellPower_six_6, bellPower_six_7,
    bellSquareEGFCoeff, Nat.factorial, Nat.bell, partitionBell_three,
    partitionBell_four, partitionBell_five, partitionBell_six, partitionBell_seven]

theorem bellPower_seven_2 :
    bellSquarePowerCoeffRec 7 2 = (0 : ℚ) := by
  rw [show 7 = 6 + 1 by omega, bellSquarePowerCoeffRec_succ,
    Finset.Nat.antidiagonal_eq_map]
  norm_num [Finset.sum_range_succ, bellPower_six_0, bellPower_six_1, bellPower_six_2, bellPower_six_3, bellPower_six_4, bellPower_six_5, bellPower_six_6, bellPower_six_7,
    bellSquareEGFCoeff, Nat.factorial, Nat.bell, partitionBell_three,
    partitionBell_four, partitionBell_five, partitionBell_six, partitionBell_seven]

theorem bellPower_seven_3 :
    bellSquarePowerCoeffRec 7 3 = (0 : ℚ) := by
  rw [show 7 = 6 + 1 by omega, bellSquarePowerCoeffRec_succ,
    Finset.Nat.antidiagonal_eq_map]
  norm_num [Finset.sum_range_succ, bellPower_six_0, bellPower_six_1, bellPower_six_2, bellPower_six_3, bellPower_six_4, bellPower_six_5, bellPower_six_6, bellPower_six_7,
    bellSquareEGFCoeff, Nat.factorial, Nat.bell, partitionBell_three,
    partitionBell_four, partitionBell_five, partitionBell_six, partitionBell_seven]

theorem bellPower_seven_4 :
    bellSquarePowerCoeffRec 7 4 = (0 : ℚ) := by
  rw [show 7 = 6 + 1 by omega, bellSquarePowerCoeffRec_succ,
    Finset.Nat.antidiagonal_eq_map]
  norm_num [Finset.sum_range_succ, bellPower_six_0, bellPower_six_1, bellPower_six_2, bellPower_six_3, bellPower_six_4, bellPower_six_5, bellPower_six_6, bellPower_six_7,
    bellSquareEGFCoeff, Nat.factorial, Nat.bell, partitionBell_three,
    partitionBell_four, partitionBell_five, partitionBell_six, partitionBell_seven]

theorem bellPower_seven_5 :
    bellSquarePowerCoeffRec 7 5 = (0 : ℚ) := by
  rw [show 7 = 6 + 1 by omega, bellSquarePowerCoeffRec_succ,
    Finset.Nat.antidiagonal_eq_map]
  norm_num [Finset.sum_range_succ, bellPower_six_0, bellPower_six_1, bellPower_six_2, bellPower_six_3, bellPower_six_4, bellPower_six_5, bellPower_six_6, bellPower_six_7,
    bellSquareEGFCoeff, Nat.factorial, Nat.bell, partitionBell_three,
    partitionBell_four, partitionBell_five, partitionBell_six, partitionBell_seven]

theorem bellPower_seven_6 :
    bellSquarePowerCoeffRec 7 6 = (0 : ℚ) := by
  rw [show 7 = 6 + 1 by omega, bellSquarePowerCoeffRec_succ,
    Finset.Nat.antidiagonal_eq_map]
  norm_num [Finset.sum_range_succ, bellPower_six_0, bellPower_six_1, bellPower_six_2, bellPower_six_3, bellPower_six_4, bellPower_six_5, bellPower_six_6, bellPower_six_7,
    bellSquareEGFCoeff, Nat.factorial, Nat.bell, partitionBell_three,
    partitionBell_four, partitionBell_five, partitionBell_six, partitionBell_seven]

theorem bellPower_seven_7 :
    bellSquarePowerCoeffRec 7 7 = (1 : ℚ) := by
  rw [show 7 = 6 + 1 by omega, bellSquarePowerCoeffRec_succ,
    Finset.Nat.antidiagonal_eq_map]
  norm_num [Finset.sum_range_succ, bellPower_six_0, bellPower_six_1, bellPower_six_2, bellPower_six_3, bellPower_six_4, bellPower_six_5, bellPower_six_6, bellPower_six_7,
    bellSquareEGFCoeff, Nat.factorial, Nat.bell, partitionBell_three,
    partitionBell_four, partitionBell_five, partitionBell_six, partitionBell_seven]

end BooleanAntichainsKernel
