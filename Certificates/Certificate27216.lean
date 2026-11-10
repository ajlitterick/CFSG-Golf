module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.SuzN0Defs
import Certificates.Kernel.Sporadic.OddCore.Suz27216G

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.SuzN0 in
theorem certificate27216 : SuzN0Facts := KernelSpor.N27216.facts

end Certificates
