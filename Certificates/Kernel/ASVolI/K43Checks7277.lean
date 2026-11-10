module

public import Certificates.Data.Kernel.ASVolI.K43K7277
public import Certificates.Kernel.HMathieu.T24
import CFSG.Certificates.Kernel.Common.EachTrue
import all Init.Data.Array.Basic
import all Init.Data.List.Basic

public section

namespace CertificateChecks.KernelASVolI

open CFSG.KS.ASVolI CertificateChecks.KernelHMathieu


end CertificateChecks.KernelASVolI

#kc_each CertificateChecks.KernelASVolI k43f4_ (fun i => CFSG.KS.ASVolI.f4Slice i) 0 32

end
