module

public import Certificates.Kernel.SporSch.HeT.X2114
public import Certificates.Kernel.LocalComp.Child3Gen
public import Certificates.Data.Kernel.KGC31PB
public import Certificates.Data.Kernel.J2Cover
public import Certificates.Data.HeldMixedInvolution
public meta import Certificates.Kernel.SporSch.Mathieu.Gen
public meta import CFSG.Sporadic.HeldB.InnerData
public meta import Certificates.Data.HeldMixedInvolution
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelHeMix

open CFSG.KS.SporSch.MOCG CFSG.Sporadic.HeldB

meta def MG : Array (Array Nat) := Mixed.generatorIndices.map fun j => heInnerSigma1.getD j #[]

meta def MRL : List (Array Nat) := Mixed.mixedWords.map (evalW 42 MG)

end CertificateChecks.KernelHeMix

#lc_reps CertificateChecks.KernelHeMix.MR 6 CertificateChecks.KernelHeMix.MG
  CertificateChecks.KernelHeMix.MRL

namespace CertificateChecks.KernelHeMix

open CFSG.KC.Enum CFSG.KS CFSG.KC.KGC31P CertificateChecks.KernelSporSch.HeX14


end CertificateChecks.KernelHeMix

end
