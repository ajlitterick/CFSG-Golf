module

public import Certificates.Kernel.Sporadic.OddCore.HeL2
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

open CFSG.PSL3Four.Native CFSG.Sporadic.SmallOddCore CFSG.ComponentClassification.GrSLit.HeldFix

meta def u1M : Array (Array Nat) := heU1Tabs ()

meta def u2M : Array (Array Nat) := heU2Tabs ()

meta def id42M : Array Nat := idTab 42

meta def normPosM (U : Array Tab) (first : Bool) : Array (Array Nat) :=
  let idx := indexOf (enumBFS 42 U 8).tabs
  ((List.range 9).toArray.map fun j => (List.range 3).toArray.map fun i =>
    let x := if first then conjTab 42 heXTabs[j]! heXInvs[j]! U[i]!
      else conjTab 42 heXInvs[j]! heXTabs[j]! U[i]!
    #[idx.getD x 0]).flatten

meta def np11M : Array (Array Nat) := normPosM (heU1Tabs ()) true

meta def np12M : Array (Array Nat) := normPosM (heU1Tabs ()) false

meta def np21M : Array (Array Nat) := normPosM (heU2Tabs ()) true

meta def np22M : Array (Array Nat) := normPosM (heU2Tabs ()) false

end CertificateChecks.KernelLC.HeE16

#kpenum CertificateChecks.KernelLC.HU1E 42 6 false CertificateChecks.KernelLC.HeE16.u1M
  CertificateChecks.KernelLC.HeE16.u1M CertificateChecks.KernelLC.HeE16.id42M 8

#kpenum CertificateChecks.KernelLC.HU2E 42 6 false CertificateChecks.KernelLC.HeE16.u2M
  CertificateChecks.KernelLC.HeE16.u2M CertificateChecks.KernelLC.HeE16.id42M 8

#kmisc_packarrs CertificateChecks.KernelLC.HeE16.NP11 CertificateChecks.KernelLC.HeE16.np11M 32

#kmisc_packarrs CertificateChecks.KernelLC.HeE16.NP12 CertificateChecks.KernelLC.HeE16.np12M 32

#kmisc_packarrs CertificateChecks.KernelLC.HeE16.NP21 CertificateChecks.KernelLC.HeE16.np21M 32

#kmisc_packarrs CertificateChecks.KernelLC.HeE16.NP22 CertificateChecks.KernelLC.HeE16.np22M 32

namespace CertificateChecks.KernelLC.HeE16

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CertificateChecks.KernelSpor


end CertificateChecks.KernelLC.HeE16

end
