
module

public import Certificates.Kernel.SporSch.Co2M.WordsBase
public import Certificates.Data.Kernel.Co2InvS
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelSporSch.Co2M

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Co2M CFSG.KC.Co2InvS

@[expose] noncomputable def swap01 (P : ℕ) : ℕ :=
  (fun x => Nat.xor P (Nat.lor x (Nat.shiftLeft x 12)))
    (Nat.xor (pg 12 (mask 12) P 0) (pg 12 (mask 12) P 1))


theorem neg_sift : notK (siftS (swap01 (WQ 0))) = true := by quickRfl


end CertificateChecks.KernelSporSch.Co2M

end
