module

public import Certificates.Kernel.O8Twin.PPairs
import Init.Data.List.SplitOn.Basic

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8Twin

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch.MOC CFSG.KC.Child3
open CFSG.KS.M11 CFSG.KS.SporSch.MBT CFSG.KC.KGC31P CFSG.KC.S7TwinK

theorem kN : Nat.beq (ordK ST.LR 5) 4096 = true := by decide +kernel


end CertificateChecks.KernelO8Twin

end
