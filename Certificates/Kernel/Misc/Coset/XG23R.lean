module

public import Certificates.Data.Kernel.Bounds.Table
public import CFSG.Certificates.Kernel.Bounds.XG23R.Route
public import CFSG.Certificates.Kernel.Bounds.XG23R.T1vC0
public import CFSG.Certificates.Kernel.Bounds.XG23R.T1vC1
public import CFSG.Certificates.Kernel.Bounds.XG23R.T1vW0
import Certificates.Kernel.Bounds.Assemble
import CFSG.Certificates.Kernel.Bounds.XG23R.All

public section

#kb_cert CFSG.KBRoute.XG23R T1 XG23R_T1v include_bytes "../../../../CFSG/Certificates/Kernel/Bounds/XG23R/data/XG23R_T1v.meta" 120408 1930638362444289591 CFSG.KBRoute.XG23R.rels

namespace CertificateChecks.KernelMiscCoset.XG23R

theorem t1 : CFSG.KBRoute.XG23R.T1.ok = true := by kb_assemble XG23R_T1v

end CertificateChecks.KernelMiscCoset.XG23R

end
