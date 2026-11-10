module

public import Certificates.Data.Kernel.Bounds.Table
public import CFSG.Certificates.Kernel.Bounds.XONU.Route
public import CFSG.Certificates.Kernel.Bounds.XONU.T1vC0
public import CFSG.Certificates.Kernel.Bounds.XONU.T1vW0
public import CFSG.Certificates.Kernel.Bounds.XONU.T1vW1
public import CFSG.Certificates.Kernel.Bounds.XONU.T1vW2
public import CFSG.Certificates.Kernel.Bounds.XONU.T1vW3
public import CFSG.Certificates.Kernel.Bounds.XONU.T1vW4
import Certificates.Kernel.Bounds.Assemble
import CFSG.Certificates.Kernel.Bounds.XONU.All

public section

#kb_cert CFSG.KBRoute.XONU T1 XONU_T1v include_bytes "../../../../CFSG/Certificates/Kernel/Bounds/XONU/data/XONU_T1v.meta" 276484 16117330287017658704 CFSG.KBRoute.XONU.rels

namespace CertificateChecks.KernelMiscCoset.XONU

theorem t1 : CFSG.KBRoute.XONU.T1.ok = true := by kb_assemble XONU_T1v

end CertificateChecks.KernelMiscCoset.XONU

end
