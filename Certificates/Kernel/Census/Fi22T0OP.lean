module

public import Certificates.Kernel.Census.Fi22RDefsT0
public import Certificates.Data.Kernel.Census.PackedRootP
import Init.Data.Nat.Fold
import Init.Data.Range.Basic
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelCensus.Fi22K.T0

set_option maxRecDepth 1000000

open CFSG.KC.Census CFSG.ComponentClassification.RankTwoSporadic.Fi22 CertificateChecks.KernelCensus.Fi22K

theorem kFit : fitsB fi22T0Root.ukc = true := by quickRfl

theorem kOP0 : pordBlkP 3510 12 fi22T0Root 0 512 = true := by quickRfl
theorem kOP1 : pordBlkP 3510 12 fi22T0Root 512 512 = true := by quickRfl
theorem kOP2 : pordBlkP 3510 12 fi22T0Root 1024 512 = true := by quickRfl
theorem kOP3 : pordBlkP 3510 12 fi22T0Root 1536 512 = true := by quickRfl
theorem kOP4 : pordBlkP 3510 12 fi22T0Root 2048 512 = true := by quickRfl
theorem kOP5 : pordBlkP 3510 12 fi22T0Root 2560 512 = true := by quickRfl
theorem kOP6 : pordBlkP 3510 12 fi22T0Root 3072 512 = true := by quickRfl
theorem kOP7 : pordBlkP 3510 12 fi22T0Root 3584 512 = true := by quickRfl
theorem kOP8 : pordBlkP 3510 12 fi22T0Root 4096 62 = true := by quickRfl

end CertificateChecks.KernelCensus.Fi22K.T0

end
