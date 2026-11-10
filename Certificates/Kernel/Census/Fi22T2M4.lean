module

public import Certificates.Kernel.Census.Fi22RDefsT2
import Init.Data.Nat.Fold
import Init.Data.Range.Basic
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelCensus.Fi22K.T2

set_option maxRecDepth 1000000

open CFSG.KC.Census CFSG.ComponentClassification.RankTwoSporadic.Fi22 CertificateChecks.KernelCensus.Fi22K

theorem kM0c : (Nat.beq fi22T2Root.perfs.size 0 && fi22T2Root.cands.toList.all (RootWitP.inRange fi22T2Root) &&
    Nat.beq fi22T2Root.wt.flatten.length (2 ^ fi22T2Root.xs.length) &&
    Nat.beq (usize fi22T2Root.ukc) fi22T2Root.im.length) = true := by
  quickRfl

end CertificateChecks.KernelCensus.Fi22K.T2

end
