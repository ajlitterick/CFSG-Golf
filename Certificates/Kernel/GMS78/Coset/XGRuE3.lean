module

public import Certificates.Data.Kernel.Bounds.Table
public import CFSG.Certificates.Kernel.Bounds.XGRuE3.Route
public import CFSG.Certificates.Kernel.Bounds.XGRuE3.T1vC0
public import CFSG.Certificates.Kernel.Bounds.XGRuE3.T1vW0
public import CFSG.Certificates.Kernel.Bounds.XGRuE3.T1vW1
public import CFSG.Certificates.Kernel.Bounds.XGRuE3.T1vW2
import Certificates.Kernel.Bounds.Assemble
import CFSG.Certificates.Kernel.Bounds.XGRuE3.All

public section

#kb_cert CFSG.KBRoute.XGRuE3 T1 XGRuE3_T1v include_bytes "../../../../CFSG/Certificates/Kernel/Bounds/XGRuE3/data/XGRuE3_T1v.meta" 166729 14091203715243916913 CFSG.KBRoute.XGRuE3.rels

namespace CertificateChecks.KernelMiscCoset.XGRuE3

theorem t1 : CFSG.KBRoute.XGRuE3.T1.ok = true := by kb_assemble XGRuE3_T1v

end CertificateChecks.KernelMiscCoset.XGRuE3

end
