import BooleanAntichainsKernel.PartitionBellCount

namespace BooleanAntichainsKernel

theorem partitionBell_three : Nat.bell 3 = 5 := by
  rw [show 3 = 2 + 1 by omega, Nat.bell_succ, ← Nat.range_succ_eq_Iic]
  norm_num [Finset.sum_range_succ]

theorem partitionBell_four : Nat.bell 4 = 15 := by
  rw [show 4 = 3 + 1 by omega, Nat.bell_succ, ← Nat.range_succ_eq_Iic]
  norm_num [Finset.sum_range_succ, partitionBell_three]

theorem partitionBell_five : Nat.bell 5 = 52 := by
  rw [show 5 = 4 + 1 by omega, Nat.bell_succ, ← Nat.range_succ_eq_Iic]
  norm_num [Finset.sum_range_succ, Nat.choose, partitionBell_three, partitionBell_four]

theorem partitionBell_six : Nat.bell 6 = 203 := by
  rw [show 6 = 5 + 1 by omega, Nat.bell_succ, ← Nat.range_succ_eq_Iic]
  norm_num [Finset.sum_range_succ, Nat.choose, partitionBell_three, partitionBell_four, partitionBell_five]

theorem partitionBell_seven : Nat.bell 7 = 877 := by
  rw [show 7 = 6 + 1 by omega, Nat.bell_succ, ← Nat.range_succ_eq_Iic]
  norm_num [Finset.sum_range_succ, Nat.choose, partitionBell_three, partitionBell_four,
    partitionBell_five, partitionBell_six]

end BooleanAntichainsKernel
