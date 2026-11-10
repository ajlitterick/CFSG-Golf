module

public import Certificates.Kernel.U52.LettersF
public import CFSG.Certificates.Kernel.U52.EvSound
import CFSG.Certificates.Kernel.Misc.ArrBind
import CFSG.Certificates.Kernel.LocalQTCovTPrim

public section

namespace CertificateChecks.KernelU52F

open CFSG.ASVolI CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.WordF CFSG.KC.Misc.ArrEnum


theorem lf_range : ∀ i < 5, ∀ x < 462,
    pg 9 (mask 9) (LFP i) x < 462 ∧ pg 9 (mask 9) (LFPI i) x < 462 := fun i hi x hx =>
  ⟨((CFSG.KC.LQT.Cov.T.perm_facts (allN_spec lfPerm i hi)).1 x hx).1,
    ((CFSG.KC.LQT.Cov.T.perm_facts (allN_spec lfiPerm i hi)).1 x hx).1⟩


end CertificateChecks.KernelU52F

end
