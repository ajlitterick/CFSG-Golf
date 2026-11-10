module

public import Certificates.Kernel.Census.Fi22RDefsT2
import Init.Data.Nat.Fold
import Init.Data.Range.Basic
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelCensus.Fi22K.T2

set_option maxRecDepth 1000000

open CFSG.KC.Census CFSG.ComponentClassification.RankTwoSporadic.Fi22 CertificateChecks.KernelCensus.Fi22K

theorem kH0 : ppcHeadAt 3510 12 (fi22T2Xs.drop 0) (fi22T2Rs.drop 0) (fi22T2Cjs.drop 0)
    (fi22T2Bs.drop 0) = true := by
  quickRfl

theorem kH1 : ppcHeadAt 3510 12 (fi22T2Xs.drop 1) (fi22T2Rs.drop 1) (fi22T2Cjs.drop 1)
    (fi22T2Bs.drop 1) = true := by
  quickRfl

end CertificateChecks.KernelCensus.Fi22K.T2

end
