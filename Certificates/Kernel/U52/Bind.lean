module

public import Certificates.Kernel.U52.Letters
public import CFSG.Certificates.Kernel.U52.EvSound
import CFSG.Certificates.Kernel.Misc.ArrBind
import CFSG.Certificates.Kernel.LocalQTCovTPrim

public section

namespace CertificateChecks.KernelU52

open CFSG.ASVolI CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.WordF CFSG.KC.Misc.ArrEnum


theorem l_range : ∀ i < 4, ∀ x < 462,
    pg 9 (mask 9) (LP i) x < 462 ∧ pg 9 (mask 9) (LPI i) x < 462 := fun i hi x hx =>
  ⟨((CFSG.KC.LQT.Cov.T.perm_facts (allN_spec lpPerm i hi)).1 x hx).1,
    ((CFSG.KC.LQT.Cov.T.perm_facts (allN_spec lpiPerm i hi)).1 x hx).1⟩


end CertificateChecks.KernelU52

end
