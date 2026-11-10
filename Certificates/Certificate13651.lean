module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThCentSound
import Certificates.Kernel.ThCent.Consumers
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThCentSoundBase2
public import CFSG.Sporadic.Th.CertificateBase
public import CFSG.Sporadic.ThSchreier.KernelAut
public import CFSG.Sporadic.ThSchreier.KernelAutBase1

public section

namespace Certificates

open CertificateChecks

theorem certificate13651 : 
    Nat.card (Subgroup.centralizer
      ({CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThCent.zJ} : Set CFSG.Sporadic.Th.J)) ≤
        472392 :=
  KernelThCent.card_centralizer_zJ_le th_kernel_facts_ok

end Certificates
