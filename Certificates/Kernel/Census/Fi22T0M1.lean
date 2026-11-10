module

public import Certificates.Kernel.Census.Fi22RDefsT0
import Init.Data.Nat.Fold
import Init.Data.Range.Basic
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelCensus.Fi22K.T0

set_option maxRecDepth 1000000

open CFSG.KC.Census CFSG.ComponentClassification.RankTwoSporadic.Fi22 CertificateChecks.KernelCensus.Fi22K

theorem kM1 : fi22T0Root.xs.all (fun g => pcommA 3510 12 g fi22T0Root.x && inWK g) = true := by
  quickRfl

theorem kM1k : (Nat.blt 13 fi22T0Root.xs.length &&
    (List.range fi22T0Root.xs.length).all fun i => Nat.beq i 13 || inXK fi22T0Root.xs[i]!) = true := by
  quickRfl

end CertificateChecks.KernelCensus.Fi22K.T0

end
