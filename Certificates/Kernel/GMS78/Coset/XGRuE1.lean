module

public import Certificates.Data.Kernel.Bounds.Table
public import CFSG.Certificates.Kernel.Bounds.XGRuE1.Route
public import CFSG.Certificates.Kernel.Bounds.XGRuE1.T1vC0
public import CFSG.Certificates.Kernel.Bounds.XGRuE1.T1vW0
public import CFSG.Certificates.Kernel.Bounds.XGRuE1.T1vW1
public import CFSG.Certificates.Kernel.Bounds.XGRuE1.T1vW2
public import CFSG.Certificates.Kernel.Bounds.XGRuE1.T1vW3
import Certificates.Kernel.Bounds.Assemble
import CFSG.Certificates.Kernel.Bounds.XGRuE1.All

public section

#kb_cert CFSG.KBRoute.XGRuE1 T1 XGRuE1_T1v include_bytes "../../../../CFSG/Certificates/Kernel/Bounds/XGRuE1/data/XGRuE1_T1v.meta" 211743 3888154857150819772 CFSG.KBRoute.XGRuE1.rels

namespace CertificateChecks.KernelMiscCoset.XGRuE1

theorem t1 : CFSG.KBRoute.XGRuE1.T1.ok = true := by kb_assemble XGRuE1_T1v

end CertificateChecks.KernelMiscCoset.XGRuE1

end
