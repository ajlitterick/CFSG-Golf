module

public import CFSG.Milestones.ASVolI.F48.Rest.U52Inputs
import Certificates.Kernel.U52.GlueX
import Certificates.Kernel.U52.ChainSub
import CFSG.Certificates.Kernel.Misc.PtOrbFSound
import CFSG.Certificates.Kernel.Spor.RawSiftK
public import CFSG.LieType.BorelTits.CompleteFlag

set_option maxRecDepth 400000

namespace CertificateChecks.Batch7769

open CFSG.ASVolI CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.WordF CFSG.KC.PtOrb
  CertificateChecks.KernelU52 CertificateChecks.KernelU52G


noncomputable def hAP (j : Nat) : Nat :=
  evFK 462 9 (mask 9) (pidn 462 9) CX.S CX.SI (burnsideF48t_u52HA.getD j [])

noncomputable def hBP (j : Nat) : Nat :=
  evFK 462 9 (mask 9) (pidn 462 9) CX.S CX.SI (burnsideF48t_u52HB.getD j [])


abbrev R : Nat := 40


theorem hPerm : allN 2 (fun j => permOK 462 9 (mask 9) (462 * 9) (hAP j)
    (pinvS 462 9 (mask 9) (hAP j))) = true ∧
    allN 2 (fun j => permOK 462 9 (mask 9) (462 * 9) (hBP j)
      (pinvS 462 9 (mask 9) (hBP j))) = true :=
  ⟨by quickRfl, by quickRfl⟩


end CertificateChecks.Batch7769

public section

namespace Certificates


end Certificates

end
