import BooleanAntichainsKernel.BellSquareCoefficientRecurrence
import BooleanAntichainsKernel.PartitionBellSmall

namespace BooleanAntichainsKernel

theorem bellSquareLogCoeffRec_four : bellSquareLogCoeffRec 4 = 119 / 24 := by
  norm_num [bellSquareLogCoeffRec, bellSquarePowerCoeffRec, bellSquareEGFCoeff,
    Finset.Nat.antidiagonal_eq_map, Finset.sum_range_succ, Nat.factorial,
    partitionBell_three, partitionBell_four]

theorem bellSquareLogCoeffRec_five : bellSquareLogCoeffRec 5 = 1343 / 120 := by
  norm_num [bellSquareLogCoeffRec, bellSquarePowerCoeffRec, bellSquareEGFCoeff,
    Finset.Nat.antidiagonal_eq_map, Finset.sum_range_succ, Nat.factorial,
    partitionBell_three, partitionBell_four, partitionBell_five]

end BooleanAntichainsKernel
