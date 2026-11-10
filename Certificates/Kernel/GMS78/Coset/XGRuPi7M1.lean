module

public import Certificates.Data.Kernel.Bounds.Table
public import CFSG.Certificates.Kernel.Bounds.XGRuPi7M1.Route
public import CFSG.Certificates.Kernel.Bounds.XGRuPi7M1.T1vC0
public import CFSG.Certificates.Kernel.Bounds.XGRuPi7M1.T1vC1
public import CFSG.Certificates.Kernel.Bounds.XGRuPi7M1.T1vW0
public import CFSG.Certificates.Kernel.Bounds.XGRuPi7M1.T1vW1
public import CFSG.Certificates.Kernel.Bounds.XGRuPi7M1.T1vW2
public import CFSG.Certificates.Kernel.Bounds.XGRuPi7M1.T1vW3
public import CFSG.Certificates.Kernel.Bounds.XGRuPi7M1.T1vW4
public import CFSG.Certificates.Kernel.Bounds.XGRuPi7M1.T1vW5
public import CFSG.Certificates.Kernel.Bounds.XGRuPi7M1.T1vW6
public import CFSG.Certificates.Kernel.Bounds.XGRuPi7M1.T1vW7
public import CFSG.Certificates.Kernel.Bounds.XGRuPi7M1.T1vW8
import Certificates.Kernel.Bounds.Assemble
import CFSG.Certificates.Kernel.Bounds.XGRuPi7M1.All

public section

#kb_cert CFSG.KBRoute.XGRuPi7M1 T1 XGRuPi7M1_T1v include_bytes "../../../../CFSG/Certificates/Kernel/Bounds/XGRuPi7M1/data/XGRuPi7M1_T1v.meta" 606611 4042253808930214429 CFSG.KBRoute.XGRuPi7M1.rels

namespace CertificateChecks.KernelMiscCoset.XGRuPi7M1

theorem t1 : CFSG.KBRoute.XGRuPi7M1.T1.ok = true := by kb_assemble XGRuPi7M1_T1v

end CertificateChecks.KernelMiscCoset.XGRuPi7M1

end
