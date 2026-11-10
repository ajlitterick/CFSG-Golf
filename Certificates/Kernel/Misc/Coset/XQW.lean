module

public import Certificates.Data.Kernel.Bounds.Table
public import CFSG.Certificates.Kernel.Bounds.XQW.Route
public import CFSG.Certificates.Kernel.Bounds.XQW.T1vC0
public import CFSG.Certificates.Kernel.Bounds.XQW.T1vW0
public import CFSG.Certificates.Kernel.Bounds.XQW.T1vW1
public import CFSG.Certificates.Kernel.Bounds.XQW.T1vW2
public import CFSG.Certificates.Kernel.Bounds.XQW.T1vW3
public import CFSG.Certificates.Kernel.Bounds.XQW.T1vW4
import Certificates.Kernel.Bounds.Assemble
import CFSG.Certificates.Kernel.Bounds.XQW.All

public section

#kb_cert CFSG.KBRoute.XQW T1 XQW_T1v include_bytes "../../../../CFSG/Certificates/Kernel/Bounds/XQW/data/XQW_T1v.meta" 275056 5348060446428055382 CFSG.KBRoute.XQW.rels

namespace CertificateChecks.KernelMiscCoset.XQW

theorem t1 : CFSG.KBRoute.XQW.T1.ok = true := by kb_assemble XQW_T1v

end CertificateChecks.KernelMiscCoset.XQW

end
