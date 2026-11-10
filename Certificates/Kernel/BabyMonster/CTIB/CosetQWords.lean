module

public import Certificates.Kernel.BabyMonster.CTIB.CosetQData
public import Certificates.Data.Kernel.BabyMonster.CTIB.CosetQ
public import Certificates.Kernel.LocalComp.BlockTac
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelBM.CTIB

open CFSG.KC.BM CFSG.KC.BM.CosetQ

theorem cqw_cts : ∀ s < 17, ctOK LOq Syms CTs s = true := by lc_cover 17

theorem cqw_syms : symsOK LOq Syms CTs = true := by quickRfl

theorem cqw_words : ∀ t < 45, wOK LOq Syms CTs Steps Gs t = true := by lc_cover 1


end CertificateChecks.KernelBM.CTIB

end
