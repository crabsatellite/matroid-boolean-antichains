import BooleanAntichainsKernel.UniformComputableFormula

namespace BooleanAntichainsKernel

set_option maxRecDepth 4096 in
/-- Kernel reduction of the proved finite profile sum for U(4,5), size 3. -/
theorem uniform45_triples_value : uniformBoundedEnumerator 5 4 3 = 50 := by
  decide

end BooleanAntichainsKernel
