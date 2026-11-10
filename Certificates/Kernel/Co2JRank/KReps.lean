module

public import Certificates.Kernel.Co2JRank.KRepData
public import Certificates.Kernel.Co2JRank.Data
public import Certificates.Data.Kernel.Co2Fuse
public import Certificates.Data.Kernel.Co2J
import CFSG.Certificates.Kernel.Common.Cover
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelSpor.Co2JRank

open CFSG.KC.Co2InvS CFSG.KC.Co2Fuse CFSG.KC.Co2J CertificateChecks.KernelSpor.Co2Syl

@[expose] noncomputable def kRepK (C : Nat → Nat) (i : Nat) : Bool :=
  andK (rkS (Nat.xor (RP i) IDP) (C (Nat.mul 3 i)))
    (andK (rkS (Nat.xor (mulV (RP i) (RP 0)) IDP) (C (Nat.add (Nat.mul 3 i) 1)))
      (rkS (mulV (Nat.xor (RP 0) IDP) (Nat.xor (RP i) IDP)) (C (Nat.add (Nat.mul 3 i) 2))))

theorem kReps : ∀ i < 10, kRepK KR i = true := by kc_cover 10

@[expose] noncomputable def wGenK (G : Nat → Nat) : Bool :=
  andK (allK (nat_lit 5) fun i => Nat.beq (mulV (G i) (G i)) IDP)
    (allK (nat_lit 5) fun i => allK (nat_lit 5) fun k =>
      Nat.beq (mulV (G i) (G k)) (mulV (G k) (G i)))

theorem wGen : wGenK WG = true := by quickRfl


end CertificateChecks.KernelSpor.Co2JRank

end
