module

public import Certificates.Kernel.LocalComp.HeFix
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Data.Kernel.Spor.PEnumX
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldFixTwoBE16Inputs
meta import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldFixTwoBE16Inputs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldFixTwoBStr
meta import CFSG.GroupTheory.LocalCores.Fitting
meta import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldFixTwoBStr

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.HeE16

open CFSG.PSL3Four.Native CFSG.ComponentClassification.GrSLit.HeldFix

meta def liftM : Array (Array Nat) := (List.range 6).toArray.map heLiftTab

end CertificateChecks.KernelLC.HeE16

#kmisc_packarrs CertificateChecks.KernelLC.HeE16.LP CertificateChecks.KernelLC.HeE16.liftM 14

namespace CertificateChecks.KernelLC.HeE16

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KC.PermTool CertificateChecks.KernelLC.HeFix
open CFSG.Sporadic.SmallOddCore


end CertificateChecks.KernelLC.HeE16

end
