module

public import Certificates.Kernel.Census.Fi22RDefsT0
import Init.Data.Nat.Fold
import Init.Data.Range.Basic
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelCensus.Fi22K.T0

set_option maxRecDepth 1000000

open CFSG.KC.Census CFSG.ComponentClassification.RankTwoSporadic.Fi22 CertificateChecks.KernelCensus.Fi22K

theorem kM0c : (Nat.beq fi22T0Root.perfs.size 0 && fi22T0Root.cands.toList.all (RootWitP.inRange fi22T0Root) &&
    Nat.beq fi22T0Root.wt.flatten.length (2 ^ fi22T0Root.xs.length) &&
    Nat.beq (usize fi22T0Root.ukc) fi22T0Root.im.length) = true := by
  quickRfl

end CertificateChecks.KernelCensus.Fi22K.T0

end
