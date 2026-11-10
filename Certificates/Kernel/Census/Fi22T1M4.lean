module

public import Certificates.Kernel.Census.Fi22RDefsT1
import Init.Data.Nat.Fold
import Init.Data.Range.Basic
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelCensus.Fi22K.T1

set_option maxRecDepth 1000000

open CFSG.KC.Census CFSG.ComponentClassification.RankTwoSporadic.Fi22 CertificateChecks.KernelCensus.Fi22K

theorem kM0c : (Nat.beq fi22T1Root.perfs.size 0 && fi22T1Root.cands.toList.all (RootWitP.inRange fi22T1Root) &&
    Nat.beq fi22T1Root.wt.flatten.length (2 ^ fi22T1Root.xs.length) &&
    Nat.beq (usize fi22T1Root.ukc) fi22T1Root.im.length) = true := by
  quickRfl

end CertificateChecks.KernelCensus.Fi22K.T1

end
