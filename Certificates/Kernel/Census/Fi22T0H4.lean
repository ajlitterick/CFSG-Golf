module

public import Certificates.Kernel.Census.Fi22RDefsT0
import Init.Data.Nat.Fold
import Init.Data.Range.Basic
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelCensus.Fi22K.T0

set_option maxRecDepth 1000000

open CFSG.KC.Census CFSG.ComponentClassification.RankTwoSporadic.Fi22 CertificateChecks.KernelCensus.Fi22K

theorem kH8 : ppcHeadAt 3510 12 (fi22T0Xs.drop 8) (fi22T0Rs.drop 8) (fi22T0Cjs.drop 8)
    (fi22T0Bs.drop 8) = true := by
  quickRfl

theorem kH9 : ppcHeadAt 3510 12 (fi22T0Xs.drop 9) (fi22T0Rs.drop 9) (fi22T0Cjs.drop 9)
    (fi22T0Bs.drop 9) = true := by
  quickRfl

end CertificateChecks.KernelCensus.Fi22K.T0

end
