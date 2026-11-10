module

public import Certificates.Data.Kernel.FzFus.Codes
import CFSG.Certificates.Kernel.Common.Eval
import CFSG.Certificates.Kernel.Common.Harness
meta import Certificates.Data.Kernel.FzFus.Twin

public section

namespace CertificateChecks.KernelFzFus

open Certificates.FzJt.K Certificates.FzFus.K

#kc_eval CertificateChecks.KernelFzFus Cl Certificates.FzFus.Twin.cls
#kc_eval CertificateChecks.KernelFzFus Rw Certificates.FzFus.Twin.rows
#kc_eval CertificateChecks.KernelFzFus Pr Certificates.FzFus.Twin.pairs

theorem ch442351cls : classB Cl.W = true := by quickRfl
theorem ch442351rows : rowsB rowsT Rw.W = true := by quickRfl
theorem ch442351subs : subsB subsT = true := by quickRfl
theorem ch442351pair : p7B Pr.A Pr.P Pr.X = true := by quickRfl


end CertificateChecks.KernelFzFus
