module

public import Certificates.Data.Kernel.S1277KGm
public import Certificates.Kernel.S1277.Data
public import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Common.Lce

public section

namespace CFSG.KP.S1277Gm

open CFSG.Quasithin.H13.S127.Mod CFSG.KC.S1277Gm CFSG.KD.S1277Gm

theorem gmK_ok : eqMc gmK gmIdx = true := by quickRfl

theorem gm6P_ok : eqB6 ((gmIdx.map Mc.ofIdx).map Mc.toB6) gm6P = true := by quickRfl

theorem orbChk_ok : orbChk gm6P = true := by quickRfl


end CFSG.KP.S1277Gm

end
