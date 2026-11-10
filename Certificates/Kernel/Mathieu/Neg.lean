module

public import Certificates.Kernel.Mathieu.RootData
public import Certificates.Kernel.Mathieu.M11Chains
public import Certificates.Data.Kernel.Mathieu.SylowK
import CFSG.Certificates.Kernel.Common.Harness

namespace CertificateChecks.KernelMathieu

open CFSG.KD.Mathieu CFSG.Monster.B.Mathieu CFSG.KC.MathieuK CFSG.KS.M11

set_option maxRecDepth 400000


end CertificateChecks.KernelMathieu
