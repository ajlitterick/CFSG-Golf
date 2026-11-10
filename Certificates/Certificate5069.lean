module

public import CFSG.GH74.GLS.C3.Layer2.L5C5fInputs
import CFSG.Certificates.Kernel.L5.EngRec
import CFSG.Certificates.Kernel.L5.F5Code
import CFSG.Certificates.Kernel.L5.Sh2Grp
import Certificates.Kernel.L5.Sh2MulChecks
import Certificates.Kernel.L5.Sh2Eng0
import Certificates.Kernel.L5.Sh2Eng1
import Certificates.Kernel.L5.Sh2Eng2
import Certificates.Kernel.L5.Sh2Eng3
import Certificates.Kernel.L5.Sh2Rec0
import Certificates.Kernel.L5.Sh2Rec1
import Certificates.Kernel.L5.Sh2Rec2
import Certificates.Kernel.L5.Sh2Rec3
import Certificates.Kernel.L5.Sh2FusE
import Certificates.Kernel.L5.Sh2Fus0
import Certificates.Kernel.L5.Sh2Fus1
import Certificates.Kernel.L5.Sh2Fus2
import Certificates.Kernel.L5.Sh2Fus3

open CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2.L5 CFSG.GH74.GLS.C3.Layer2.L5.Fus CFSG.KD
  CFSG.KD.L5 CFSG.Certificates.Kernel.L5Sh2

namespace CertificateChecks.Batch5069

open CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2.L5 CFSG.GH74.GLS.C3.Layer2.L5.Fus CFSG.KD
  CFSG.KD.L5 CFSG.Certificates.Kernel.L5Sh2

local macro "tr " c:term:max ty:term:max : tactic => `(tactic|
  exact (grpOf_eq (sh2TabD $ty).grp (mulI (Fin.val $ty)) (mulI_eq' sh2MulChk_true $ty)
    (invI (Fin.val $ty)) (invI_eq sh2MulChk_true $ty) oneI (oneI_eq $ty)) ▸
    ($c (sh2TabD $ty).grp (mulI_eq' sh2MulChk_true $ty) (invI_eq sh2MulChk_true $ty)
      (oneI_eq $ty)))


end CertificateChecks.Batch5069

public section

namespace Certificates

open CertificateChecks


end Certificates
