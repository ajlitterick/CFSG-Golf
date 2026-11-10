module

public import CFSG.RankThree.PartTwo.Sec8.Item812Res3ProofSUInner
public import CFSG.RankThree.PartTwo.Sec8.Item812Res3ProofSpReal
public import CFSG.RankThree.PartTwo.Sec8.Item83ProofChoice
public import CFSG.RankThree.PartTwo.Sec8.Item812Res4ProofFusion
public import CFSG.RankThree.PartTwo.Sec8.Item812Res4ProofLocal
public import CFSG.RankThree.PartTwo.Sec8.Item812Res4ProofApply
public import CFSG.RankThree.PartTwo.Sec8.Item812Res4ProofConfig
import CFSG.RankThree.PartTwo.KFacts.KSListsProofCard
import CFSG.RankThree.PartTwo.KFacts.K71Item89

public section

namespace CFSG.RankThree.PartTwo.Sec8

theorem fin812Sylow_of_res4 (hPa : Fin812PaSplit) (hBq : Fin812BEq) (hQR : Fin812QR)
    (hBw : Fin812BWeak) (hW : KF812WreathCent) (hF : KF812E27Fuse) : Fin812Sylow :=
  fin812Sylow_of (fin812Local_of hPa hBq hQR hBw hW) (fin812FusionW_of hW)
    (fin812FusionV_of_kf hF hW) (fin812Extremal_of_kf hW)

theorem sec8Never_of_xy (h87 : Item87) (h88 : Item88) (h84 : Pair84A) (hsym : Pair84Sym)
    (hXY : Item89XY) (hcfg : Pair89InConfig) (hS : Fin812Sylow) : Sec8Never := by
  have h89 := item89_of_split h88 hXY (pair89Omega_of hXY h87 h84 hcfg)
  exact sec8Never_of h87 h88 h89 (item810_of h87 h89 pair810Center)
    (item811_of h87 h89 hsym (pair811Gen_of pair811GenSU)) hS fin812Frattini fin812XNormal h84

end CFSG.RankThree.PartTwo.Sec8
