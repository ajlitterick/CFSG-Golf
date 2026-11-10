module

public import Certificates.Data.Kernel.S1277KSig
public import Certificates.Kernel.S1277.SigData
public import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Common.Lce

public section

namespace CFSG.KP.S1277Sig

open CFSG.KC.S1277Sig CFSG.KD.S1277Sig

theorem sig_ok : sigAll sd sl sb sT = true := by quickRfl


end CFSG.KP.S1277Sig

end
