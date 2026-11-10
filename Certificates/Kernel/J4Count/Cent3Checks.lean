module

public import Certificates.Data.Kernel.J4Cent3
public import Certificates.Kernel.J4Count.FixCEData
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporJ4Data
import CFSG.Certificates.Kernel.Common.Harness
public import Mathlib.Data.Fin.Basic

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Count.Cent3

open CFSG.KC.J4Cent3 CFSG.KC.J4Five CFSG.KC.J4Q CFSG.KD.J4FixCE
open CFSG.QuasithinUnique.Vol2Native.L239.J4Pairs

theorem ce_tab : starTabOK PC starMasks ZE = true := by quickRfl

theorem ce_fix : fixOK ZE FL3 = true := by quickRfl

theorem ce_oct : oct6OK GB GP ZE FL3 TL3 = true := by quickRfl

theorem ce_crd : crd16OK ZE CRD3 (FL3 ++ TL3) = true := by quickRfl

theorem ce_dist : distB (FL3 ++ TL3) = true := by quickRfl

theorem ce_cand : Nat.beq (cand3N GB GP ZE CRD3 FL3 TL3) 1 = true := by quickRfl


end CertificateChecks.KernelJ4Count.Cent3

end
