module

public import Certificates.Data.Kernel.Co2Smith.Cox
public import Certificates.Kernel.Co2Smith.LettersData
public import Certificates.Kernel.Co2Smith.CoxData

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo2Smith

open CFSG.KC.Co2InvS CFSG.KC.Co2Smith CFSG.Sporadic.Co2Smith.Native

theorem tp_k : (glMkTWords.size == 15 && (List.range 15).all fun j =>
    (glMkTWords[j]!).all (· < 22) && eqK (TP j) (wK LP glMkTWords[j]!)) = true := by
  decide +kernel


end CertificateChecks.KernelCo2Smith
