import BooleanAntichainsKernel.UniformComputableFormula

namespace BooleanAntichainsKernel

set_option maxRecDepth 4096 in
/-- Kernel reduction of the proved finite profile sum for U(3,4), size 3. -/
theorem uniform34_top_value : uniformBoundedEnumerator 4 3 3 = 4 := by
  decide

end BooleanAntichainsKernel
