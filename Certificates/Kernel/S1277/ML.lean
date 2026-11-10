module

public import Certificates.Data.Kernel.S1277KML
public import Certificates.Kernel.S1277.Data
public import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KP.S1277ML

open CFSG.Quasithin.H13.S127.Mod CFSG.KC.S1277Gm CFSG.KD.S1277Gm CFSG.KC.S1277ML

@[expose] def m18M : ℕ := 9385823236096332062

@[expose] def m45M : ℕ := 9060920837613219552

theorem sig_ok : eqB6 ((gm6P.map B6.ofP).map (·.comp sig6)) (gm6P.map sigP) = true := by quickRfl

theorem os_ok : osChk gm6P m18M m45M = true := by quickRfl

theorem mchk_gm : mChk gm6P m18M m45M = true := by quickRfl

theorem mchk_nm : mChk (gm6P ++ gm6P.map sigP) m18M m45M = true := by quickRfl


end CFSG.KP.S1277ML

end
