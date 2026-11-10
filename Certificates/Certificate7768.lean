module

public import CFSG.Milestones.ASVolI.F48.Rest.U52Inputs
import Certificates.Kernel.U52.GlueX
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LieType.BorelTits.CompleteFlag

set_option maxRecDepth 400000

namespace CertificateChecks.Batch7768

open CFSG.ASVolI CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.WordF CertificateChecks.KernelU52
  CertificateChecks.KernelU52G

local macro "u52d" : tactic => `(tactic|
  ((repeat' (first
    | apply rPC
    | exact rE _
    | exact cE _
    | exact cPC _ _
    | exact cId)) <;> done))


end CertificateChecks.Batch7768

public section

namespace Certificates

open CertificateChecks


end Certificates

end
