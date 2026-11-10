module

public import Certificates.Data.Kernel.Hall82K.Affine
import CFSG.Certificates.Kernel.Common.EachTrue

set_option maxRecDepth 100000

public section

namespace CFSG.KC.Hall82K

theorem ch840004x1_mul : x1MulK = true := by decide +kernel

theorem ch840004x1_zero : x1ZeroK = true := by decide +kernel

theorem ch840004x1_surj : x1SurjK = true := by decide +kernel

theorem ch840004x1_sq : x1SqK = true := by decide +kernel

theorem ch840004x1_orb : x1OrbK = true := by decide +kernel

theorem ch840004c5_inv : c5InvK = true := by decide +kernel


#kc_each ch840004conj b (fun b => conjRowK b) 0 64

theorem ch840004conj_surj : conjSurjK = true := by decide +kernel


theorem ch840004lift : liftK 45451591809 51811205313 34628702724 = true := by decide +kernel


end CFSG.KC.Hall82K
