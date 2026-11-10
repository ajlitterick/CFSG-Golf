module

public import Certificates.Kernel.Census.M2217.Data
import all Certificates.Kernel.Census.M2217.Data
import all Certificates.Data.Kernel.Census.Packed
import all CFSG.Certificates.Kernel.Enum.Defs
import all Mathlib.Data.List.Sort
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelCensus.M2217

set_option maxRecDepth 1000000

theorem kWt : (List.range' 1200 39).all wordF = true := by quickRfl

end CertificateChecks.KernelCensus.M2217

end
