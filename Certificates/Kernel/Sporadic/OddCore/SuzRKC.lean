module

public import Certificates.Kernel.Sporadic.OddCore.SuzRK
public import Certificates.Data.Kernel.Spor.KEnum
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelSpor.SuzRKC

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.KEnum CertificateChecks.KernelSpor

@[expose] noncomputable def sl (s : Nat) : Bool :=
  kenumSlK 1782 11 (mask 11) (1782 * 11) 2 4 3456 SuzRKG SuzRKT SuzRKTI SuzRKPL SuzRKPOS SuzRKFP
    SuzRKSRT SuzRKSRI (Nat.mul (nat_lit 72) s) (nat_lit 72)

theorem hd : kenumHdK 1782 11 (mask 11) (1782 * 11) 2 4 3456 (pidn 1782 11) SuzRKG SuzRKT =
    true := by
  quickRfl

theorem idn : idK 1782 11 (mask 11) = true := by quickRfl

theorem gA : Nat.beq (SuzRKA.F 0) (SuzRKG 0) = true := by quickRfl

theorem gB : Nat.beq (SuzRKB.F 0) (SuzRKG 1) = true := by quickRfl

theorem iA : invEqK 1782 11 (mask 11) (1782 * 11) (SuzRKG 0) (SuzRKG 2) = true := by quickRfl

theorem iB : invEqK 1782 11 (mask 11) (1782 * 11) (SuzRKG 1) (SuzRKG 3) = true := by quickRfl


end CertificateChecks.KernelSpor.SuzRKC

end
