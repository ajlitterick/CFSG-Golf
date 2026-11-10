module

public import Certificates.Data.OmegaSplitFacts
import Certificates.Kernel.A45Cls.GlueSplit

public section

namespace Certificates

open CertificateChecks

theorem certificate442009 : OmegaSplit.Facts := KernelA45.factsSplit

end Certificates
