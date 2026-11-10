module

public import Certificates.Data.Kernel.A8Nbr476K
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelA8N476

open CFSG.KC.A8N476 Certificates.A8Nbr476

theorem ch476001_words : wordsB wordData = true := by quickRfl

theorem ch476001_cover : coverB (codesL wordData) (codesC excCases) = true := by quickRfl

theorem ch476001_mon : monB monData = true := by quickRfl

theorem ch476001_len : allCases.length = 516 := by decide +kernel

theorem ch476001_fst : monData.map Prod.fst = excCases := by decide +kernel

theorem ch476001_exc : ∀ c ∈ excCases, c ∈ allCases := by decide +kernel


end CertificateChecks.KernelA8N476

end
