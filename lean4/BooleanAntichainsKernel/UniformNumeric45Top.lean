import BooleanAntichainsKernel.UniformComputableFormula

namespace BooleanAntichainsKernel

set_option maxRecDepth 16384 in
/-- Kernel reduction of the proved finite profile sum for U(4,5), size 4. -/
theorem uniform45_top_value : uniformBoundedEnumerator 5 4 4 = 5 := by
  decide

end BooleanAntichainsKernel
