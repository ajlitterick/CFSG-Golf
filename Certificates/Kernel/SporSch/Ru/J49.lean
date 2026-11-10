module

public import Certificates.Kernel.SporSch.Ru.J49K
public import Certificates.Kernel.SporSch.Ru.G2Ru7164
public import CFSG.Certificates.Kernel.SporSch.IntLinesSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.RuJ49

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.IntLines CFSG.KC.BfsPin
  CertificateChecks.KernelSporSch.RuG CertificateChecks.KernelSporSch.G2Ru7164
  CFSG.Sporadic.RuSchreier CFSG.Sporadic.RuSchreier.J49 CFSG.Sporadic.RuSchreier.J49.Sl2
  CFSG.Monster.B.Co2.Native


end CertificateChecks.KernelSporSch.RuJ49

end
