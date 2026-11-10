module

public import Certificates.Kernel.Census.M22II.DataL
import all Certificates.Kernel.Census.M22II.DataL
import all Certificates.Kernel.Census.M22II.Data
import all Certificates.Data.Kernel.Census.PackedL
import all Certificates.Data.Kernel.Census.Packed
import all CFSG.Certificates.Kernel.Enum.Defs
import all Mathlib.Data.List.Sort
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelCensus.M22II

set_option maxRecDepth 1000000

theorem kLt : blkL 570 25 = true := by quickRfl

end CertificateChecks.KernelCensus.M22II

end
