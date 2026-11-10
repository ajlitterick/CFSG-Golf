module

public import Certificates.Kernel.Census.Fi22RDefsT1
import Init.Data.Nat.Fold
import Init.Data.Range.Basic
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelCensus.Fi22K.T1

set_option maxRecDepth 1000000

open CFSG.KC.Census CFSG.ComponentClassification.RankTwoSporadic.Fi22 CertificateChecks.KernelCensus.Fi22K

theorem kM2 : fi22T1Root.cs.toList.all (fun c => pvalid 3510 12 c && inXK c &&
    pcommA 3510 12 c fi22T1Root.x) = true := by
  quickRfl

end CertificateChecks.KernelCensus.Fi22K.T1

end
