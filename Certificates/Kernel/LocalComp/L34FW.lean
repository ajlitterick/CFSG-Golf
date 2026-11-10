module

public import Certificates.Kernel.LocalComp.L34RDefs
public import Certificates.Data.Kernel.L34FW
meta import Certificates.Kernel.LocalComp.L34FWData

public section

set_option maxRecDepth 400000

#kmisc_packarrs CertificateChecks.KernelLC.L34FW.PAR CertificateChecks.KernelLC.L34FW.parArr 9
#kmisc_packarrs CertificateChecks.KernelLC.L34FW.DEP CertificateChecks.KernelLC.L34FW.depArr 4
#kmisc_packarrs CertificateChecks.KernelLC.L34FW.GW CertificateChecks.KernelLC.L34FW.genArr 9

namespace CertificateChecks.KernelLC.L34FW

open CFSG.KC.Enum CFSG.KS CFSG.KC.L34FW CertificateChecks.KernelLC

theorem tree_k : treeK (L34O.T 0) PAR DEP = true := by decide +kernel

theorem gen_k : genK (L34O.T 0) L34R.G GW = true := by decide +kernel


end CertificateChecks.KernelLC.L34FW

end
