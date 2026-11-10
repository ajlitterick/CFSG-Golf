module

public import Certificates.Kernel.TitsOct.Glue
public import Certificates.Kernel.TitsOct.ChecksLam
public import CFSG.Certificates.Kernel.TitsOctLamSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelTitsOct

open CFSG.KC.Enum CFSG.KS CFSG.KC.TwoF4LieK CFSG.KC.TitsOctK CFSG.KC.TwoF4LieSound
  CFSG.KC.TitsOctSound CFSG.KC.TitsOctLamK CFSG.KC.TitsOctLamSound CFSG.KD.TitsOct
  CFSG.KD.TitsOctLam CFSG.Sporadic.Schreier.Tits CFSG.Quasithin CFSG.Quasithin.H13.F45Ru

local notation "TA" => CFSG.Sporadic.Schreier.Tits.titsA


end CertificateChecks.KernelTitsOct

end
