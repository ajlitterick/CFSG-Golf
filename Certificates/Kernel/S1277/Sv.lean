module

public import Certificates.Data.Kernel.S1277KSv
public import Certificates.Kernel.S1277.ModData
public import Certificates.Kernel.S1277.LatData
public import Certificates.Kernel.S1277.FrData
public import Certificates.Kernel.S1277.SvData
public import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Common.Lce
import CFSG.Certificates.Kernel.Common.EachTrue

public section

namespace CFSG.KP.S1277Sv

open CFSG.KC.S1277Lat CFSG.KC.S1277Mod CFSG.KC.S1277Sv CFSG.KD.S1277Mod CFSG.KD.S1277Lat
  CFSG.KD.S1277Fr CFSG.KD.S1277Sv

noncomputable abbrev Mn : Mdl := ⟨48, apn, cpn, ipn, onen⟩

theorem sv_s : sChk Mn kgn (sgcn.getD 4 0) (sgwn.getD 4 []) sg sl sp sj sd = true := by quickRfl

theorem sv_p : pChk sl pl pi = true := by quickRfl

theorem sv_vg : vgChk (sgln.getD 4 0) [] vg = true := by quickRfl

theorem sv_hp : hpChk vg sl sp36 hp = true := by quickRfl

theorem sv_cnt : cntChk vr vb = true := by quickRfl

theorem sv_vr : vr.length = 40 := by decide +kernel

#kc_each CFSG.KP.S1277Sv ch589103cov (covChk sp36 hp vt sl a1 a2 vr vb) 0 40

theorem sv_wS : allLt 130 (wSChk pl sg vg vt vw) = true := by quickRfl

theorem sv_wA1 : allLt 130 (wAChk pl sg vg vt k1 2 w1) = true := by quickRfl


theorem sv_a1 : aChk1 sg sl vg vt k1 2 a1 a1p a1j a1d = true := by quickRfl

theorem sv_a2 : aChk1 sg sl vg vt k2 3 a2 a2p a2j a2d = true := by quickRfl


end CFSG.KP.S1277Sv

end
