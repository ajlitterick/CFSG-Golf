module

public import Certificates.Kernel.Census.Fi22RDefsT0
import Init.Data.Nat.Fold
import Init.Data.Range.Basic
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelCensus.Fi22K.T0

set_option maxRecDepth 1000000

open CFSG.KC.Census CFSG.ComponentClassification.RankTwoSporadic.Fi22 CertificateChecks.KernelCensus.Fi22K

theorem kH16 : ppcHeadAt 3510 12 (fi22T0Xs.drop 16) (fi22T0Rs.drop 16) (fi22T0Cjs.drop 16)
    (fi22T0Bs.drop 16) = true := by
  quickRfl

theorem kH17 : ppcHeadAt 3510 12 (fi22T0Xs.drop 17) (fi22T0Rs.drop 17) (fi22T0Cjs.drop 17)
    (fi22T0Bs.drop 17) = true := by
  quickRfl

end CertificateChecks.KernelCensus.Fi22K.T0

end
