import BooleanAntichainsKernel.SubspaceComputableFormula

namespace BooleanAntichainsKernel

/-- Kernel reduction of the proved full formula over the two-element field. -/
theorem subspaceF23_singletons_value : finiteSubspaceEnumerator 2 3 1 = 15 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem subspaceF23_pairs_value : finiteSubspaceEnumerator 2 3 2 = 49 := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem subspaceF23_triples_value : finiteSubspaceEnumerator 2 3 3 = 28 := by
  decide +kernel

end BooleanAntichainsKernel
