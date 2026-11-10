module

public import Certificates.Kernel.Co1M.Base10077
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1M

open CFSG.KC.Co1M CFSG.KD.Co1M CFSG.KC.TreeK

theorem ty77_chk : treeOK (actV YT77) 2 12 om77 T77Y = true := by quickRfl


end CertificateChecks.KernelCo1M

end
