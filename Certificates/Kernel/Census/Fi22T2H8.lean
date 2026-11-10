module

public import Certificates.Kernel.Census.Fi22RDefsT2
import Init.Data.Nat.Fold
import Init.Data.Range.Basic
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelCensus.Fi22K.T2

set_option maxRecDepth 1000000

open CFSG.KC.Census CFSG.ComponentClassification.RankTwoSporadic.Fi22 CertificateChecks.KernelCensus.Fi22K

theorem kH16 : ppcHeadAt 3510 12 (fi22T2Xs.drop 16) (fi22T2Rs.drop 16) (fi22T2Cjs.drop 16)
    (fi22T2Bs.drop 16) = true := by
  quickRfl

theorem kH17 : ppcHeadAt 3510 12 (fi22T2Xs.drop 17) (fi22T2Rs.drop 17) (fi22T2Cjs.drop 17)
    (fi22T2Bs.drop 17) = true := by
  quickRfl

end CertificateChecks.KernelCensus.Fi22K.T2

end
