module

public import Certificates.Data.Kernel.Tower.L1
public import Certificates.Kernel.Tower.WData
public import Certificates.Kernel.Tower.L1Data

public section

namespace Certificates.KernelTower

open Certificates.KernelTower

theorem ch36409_l1 : l1OK slSM slAC slPS slRW slMR = true := by decide +kernel
theorem ch36409_reps : repsOK slSM slAC slMR = true := by decide +kernel
theorem ch36408_l1 : l1OK wrSM wrAC wrPS wrRW wrMR = true := by decide +kernel
theorem ch36408_reps : repsOK wrSM wrAC wrMR = true := by decide +kernel


end Certificates.KernelTower
