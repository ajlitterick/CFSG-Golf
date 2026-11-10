module

public import Certificates.Data.Kernel.F4M3B

public section

set_option profiler true
set_option profiler.threshold 500

namespace CFSG.KC.F4M3B

theorem ch7052 : chkN 18 = true := by decide +kernel


end CFSG.KC.F4M3B

end
