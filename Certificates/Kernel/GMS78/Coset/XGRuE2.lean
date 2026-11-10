module

public import Certificates.Data.Kernel.Bounds.Table
public import CFSG.Certificates.Kernel.Bounds.XGRuE2.Route
public import CFSG.Certificates.Kernel.Bounds.XGRuE2.T1vC0
public import CFSG.Certificates.Kernel.Bounds.XGRuE2.T1vW0
public import CFSG.Certificates.Kernel.Bounds.XGRuE2.T1vW1
public import CFSG.Certificates.Kernel.Bounds.XGRuE2.T1vW2
import Certificates.Kernel.Bounds.Assemble
import CFSG.Certificates.Kernel.Bounds.XGRuE2.All

public section

#kb_cert CFSG.KBRoute.XGRuE2 T1 XGRuE2_T1v include_bytes "../../../../CFSG/Certificates/Kernel/Bounds/XGRuE2/data/XGRuE2_T1v.meta" 166702 706066429356552441 CFSG.KBRoute.XGRuE2.rels

namespace CertificateChecks.KernelMiscCoset.XGRuE2

theorem t1 : CFSG.KBRoute.XGRuE2.T1.ok = true := by kb_assemble XGRuE2_T1v

end CertificateChecks.KernelMiscCoset.XGRuE2

end
