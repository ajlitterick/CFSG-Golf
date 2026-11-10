module

public import Certificates.Kernel.Co1M.Base10077
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1M

open CFSG.KC.Co1M CFSG.KD.Co1M CFSG.KC.TreeK

theorem tx77_chk : treeOK (actX H77 H77i) 2 11 TP77 T77X = true := by quickRfl


theorem tp77_chk : treeOK (actP G77) 3 5 1 T77P = true := by quickRfl


end CertificateChecks.KernelCo1M

end
