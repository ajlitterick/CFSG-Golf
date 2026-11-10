module

public import CFSG.Certificates.Kernel.DecTextSound
public import CFSG.LocalAnalysis.ComponentClassification.M12J2CoverExclusion
public import CFSG.LocalAnalysis.ComponentClassification.CentralCoverTransferCocycle
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverModelsNative
meta import Certificates.Kernel.LocalComp.NatsGen
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Foundations.QuasisimpleMulEquiv
public import Certificates.Certificate3086
public import Certificates.Certificate3139
import Certificates.Kernel.LocalComp.NatsGen

public section

#lc_natsof CertificateChecks.KernelLC.FR CFSG.ComponentClassification.J2Cover.Models.fRows

namespace CertificateChecks.KernelLC

open CFSG.KC.DecText CFSG.ComponentClassification.J2Cover.Models

theorem kFR : digitsOK FR.chars = true := by quickRfl


end CertificateChecks.KernelLC

end
