module

public import Certificates.Kernel.Co2Fuse.RepData
public import Certificates.Data.Kernel.Co2Fuse
import CFSG.Certificates.Kernel.Common.Cover
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelSpor.Co2Fuse

open CFSG.KC.Co2InvS CFSG.KC.Co2Fuse CertificateChecks.KernelSpor.Co2Syl

@[expose] def LR : Nat := 288083878177

theorem repLabs : ∀ i < 10,
    Nat.beq (labY CR (RP 0) (RP i) (Nat.mul 3 i)) (fld(LR, Nat.mul 4 i, 15)) = true := by
  kc_cover 10


end CertificateChecks.KernelSpor.Co2Fuse

end
