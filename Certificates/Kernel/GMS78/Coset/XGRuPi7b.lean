module

public import Certificates.Data.Kernel.Bounds.Table
public import CFSG.Certificates.Kernel.Bounds.XGRuPi7b.Route
public import CFSG.Certificates.Kernel.Bounds.XGRuPi7b.T1vC0
public import CFSG.Certificates.Kernel.Bounds.XGRuPi7b.T1vW0
public import CFSG.Certificates.Kernel.Bounds.XGRuPi7b.T1vW1
public import CFSG.Certificates.Kernel.Bounds.XGRuPi7b.T1vW2
public import CFSG.Certificates.Kernel.Bounds.XGRuPi7b.T1vW3
import Certificates.Kernel.Bounds.Assemble
import CFSG.Certificates.Kernel.Bounds.XGRuPi7b.All

public section

#kb_cert CFSG.KBRoute.XGRuPi7b T1 XGRuPi7b_T1v include_bytes "../../../../CFSG/Certificates/Kernel/Bounds/XGRuPi7b/data/XGRuPi7b_T1v.meta" 247976 16092381889731668133 CFSG.KBRoute.XGRuPi7b.rels

namespace CertificateChecks.KernelMiscCoset.XGRuPi7b

theorem t1 : CFSG.KBRoute.XGRuPi7b.T1.ok = true := by kb_assemble XGRuPi7b_T1v

end CertificateChecks.KernelMiscCoset.XGRuPi7b

end
