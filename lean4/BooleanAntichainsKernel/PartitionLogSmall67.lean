import BooleanAntichainsKernel.BellSquarePowerCache57

namespace BooleanAntichainsKernel

theorem bellSquareLogCoeffRec_six : bellSquareLogCoeffRec 6 = 1327 / 48 := by
  norm_num [bellSquareLogCoeffRec, Finset.sum_range_succ,
    bellSquarePowerCoeffRec_zero, bellPower_one, bellPower_two_6, bellPower_three_6,
    bellPower_four_6, bellPower_five_6, bellPower_six_6, bellPower_seven_6,
    bellSquareEGFCoeff, partitionBell_six, Nat.factorial]

theorem bellSquareLogCoeffRec_seven : bellSquareLogCoeffRec 7 = 369113 / 5040 := by
  norm_num [bellSquareLogCoeffRec, Finset.sum_range_succ,
    bellSquarePowerCoeffRec_zero, bellPower_one, bellPower_two_7, bellPower_three_7,
    bellPower_four_7, bellPower_five_7, bellPower_six_7, bellPower_seven_7,
    bellSquareEGFCoeff, partitionBell_seven, Nat.factorial]

end BooleanAntichainsKernel
