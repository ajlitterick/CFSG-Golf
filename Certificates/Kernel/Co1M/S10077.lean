module

public import Certificates.Kernel.Co1M.Base10077
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1M

open CFSG.KC.Co1M CFSG.KD.Co1M CFSG.KC.TreeK CFSG.KC.Co1F2 CFSG.KC.M1F2 CFSG.KLie.CT

theorem uni77_chk : allN 6 (fun k => uniK (mulF 24 (mulF 24 QP77 (getL 0 SR77 k)) QIP77)) = true := by
  quickRfl


theorem ts77_chk : treeOK (actV ST77) 6 11 GW77 T77S = true := by quickRfl


theorem tu77_chk : treeOK (actM UM77) 4 4 (idF 24) T77U = true := by quickRfl


end CertificateChecks.KernelCo1M

end
