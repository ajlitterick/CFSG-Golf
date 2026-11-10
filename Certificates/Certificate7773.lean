module

public import CFSG.Milestones.ASVolI.F48.Rest.U52eInputs
import Certificates.Kernel.U52.GlueX
import Certificates.Kernel.U52.BindF
import CFSG.Certificates.Kernel.Misc.ArrBind
public import CFSG.LieType.BorelTits.CompleteFlag

set_option maxRecDepth 400000

namespace CertificateChecks.Batch7773

open CFSG.ASVolI CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.WordF CFSG.KC.Misc.ArrEnum
  CertificateChecks.KernelU52 CertificateChecks.KernelU52G CertificateChecks.KernelU52F

private theorem rL5 : ∀ i < 5, Rng 462 9 (LFP i) ∧ Rng 462 9 (LFPI i) := fun i hi =>
  ⟨fun x hx => (lf_range i hi x hx).1, fun x hx => (lf_range i hi x hx).2⟩

private theorem rE5 (wd : List (Fin 5 × Bool)) :
    Rng 462 9 (evFK 462 9 (mask 9) (pidn 462 9) LFP LFPI wd) :=
  rng_evFK (by norm_num) (by norm_num) (by norm_num) rL5 wd

private theorem cE5 (wd : List (Fin 5 × Bool)) :
    Canon 462 9 (evFK 462 9 (mask 9) (pidn 462 9) LFP LFPI wd) :=
  canon_evFK (by norm_num) (by norm_num) (by norm_num) LFP LFPI wd


private theorem fPerm : permOK 462 9 (mask 9) (462 * 9) (LFP 4) (LFP 4) = true := by
  quickRfl

private theorem rF : Rng 462 9 (LFP 4) := rng_of_permOK fPerm

private theorem cF : Canon 462 9 (LFP 4) := canon_of_permOK fPerm

local macro "u52ed" : tactic => `(tactic|
  ((repeat' (first
    | exact rE _
    | exact cE _
    | exact rE5 _
    | exact cE5 _
    | exact cPC _ _
    | exact cId
    | exact rId
    | exact rF
    | exact cF
    | exact fun _ => cE _
    | exact fun _ => cE5 _
    | exact fun _ => rE _
    | exact fun _ => rE5 _
    | exact rS _ (by decide)
    | exact cS _ (by decide)
    | apply rPC
    | apply rng_getD
    | apply canon_getD)) <;> done))


end CertificateChecks.Batch7773

public section

namespace Certificates

open CertificateChecks


end Certificates

end
