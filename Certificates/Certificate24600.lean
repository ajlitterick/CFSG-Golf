module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.BetaCheck
import Certificates.Kernel.Sporadic.OddCore.C24600F
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Walter.JRFacts

public section

namespace Certificates

open CertificateChecks

theorem certificate24600 : CFSG.EvenSporadicStandard.Fin76b.Beta.j2CountComm = 1080 ∧
    CFSG.EvenSporadicStandard.Fin76b.Beta.j2CountSq = 0 :=
  ⟨KernelSpor.C24600.countComm, KernelSpor.C24600.countSq⟩

end Certificates
