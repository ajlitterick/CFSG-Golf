module

public import Certificates.Data.Kernel.Bounds.Table
public import CFSG.Certificates.Kernel.Bounds.YCt233.Route
public import CFSG.Certificates.Kernel.Bounds.YCt233.T1vC0
public import CFSG.Certificates.Kernel.Bounds.YCt233.T1vC1
public import CFSG.Certificates.Kernel.Bounds.YCt233.T1vC2
public import CFSG.Certificates.Kernel.Bounds.YCt233.T1vW0
public import CFSG.Certificates.Kernel.Bounds.YCt233.T1vW1
public import CFSG.Certificates.Kernel.Bounds.YCt233.T1vW2
public import CFSG.Certificates.Kernel.Bounds.YCt233.T1vW3
public import CFSG.Certificates.Kernel.Bounds.YCt233.T1vW4
public import CFSG.Certificates.Kernel.Bounds.YCt233.T1vW5
public import CFSG.Certificates.Kernel.Bounds.YCt233.T1vW6
public import CFSG.Certificates.Kernel.Bounds.YCt233.T1vW7
public import CFSG.Certificates.Kernel.Bounds.YCt233.T1vW8
public import CFSG.Certificates.Kernel.Bounds.YCt233.T1vW9
public import CFSG.Certificates.Kernel.Bounds.YCt233.T1vW10
public import CFSG.Certificates.Kernel.Bounds.YCt233.T1vW11
import Certificates.Kernel.Bounds.Assemble
import CFSG.Certificates.Kernel.Bounds.YCt233.All

public section

#kb_cert CFSG.KBRoute.YCt233 T1 YCt233_T1v include_bytes "../../../../CFSG/Certificates/Kernel/Bounds/YCt233/data/YCt233_T1v.meta" 843515 12715723446149309956 CFSG.KBRoute.YCt233.rels

namespace CertificateChecks.KernelYChain.YCt233

theorem t1 : CFSG.KBRoute.YCt233.T1.ok = true := by kb_assemble YCt233_T1v

end CertificateChecks.KernelYChain.YCt233

end
