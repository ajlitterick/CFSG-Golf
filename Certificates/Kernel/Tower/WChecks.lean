module

public import Certificates.Data.Kernel.Tower.W
public import Certificates.Kernel.Tower.WData
public import Certificates.Data.CFSGNative.SCATWreathData

public section

namespace Certificates.KernelTower

open Certificates.KernelTower

theorem ch36409_lp : lpOK slLP CFSG.SCATWreath.slList = true := by decide +kernel
theorem ch36409_sm : smOK slLP slSM = true := by decide +kernel
theorem ch36409_ac : acOK slLP slAC = true := by decide +kernel
theorem ch36408_lp : lpOK wrLP CFSG.SCATWreath.wrList = true := by decide +kernel
theorem ch36408_sm : smOK wrLP wrSM = true := by decide +kernel
theorem ch36408_ac : acOK wrLP wrAC = true := by decide +kernel


end Certificates.KernelTower
