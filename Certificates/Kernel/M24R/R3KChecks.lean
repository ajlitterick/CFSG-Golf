module

public import Certificates.Data.Kernel.M24R.R3K

public section

set_option profiler true
set_option profiler.threshold 200

namespace CFSG.KC.M24R3

theorem ch21194_rel : relK gP = true := by decide +kernel

theorem ch21194_id : idK gP = true := by decide +kernel

theorem ch21194_dist : distK gP = true := by decide +kernel


end CFSG.KC.M24R3

end
