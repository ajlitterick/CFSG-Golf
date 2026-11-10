module

public import CFSG.Quasithin.MS93.S38Holds
public import CFSG.Quasithin.MS93.S18Holds
public import CFSG.Quasithin.MS93.RedMain
public import CFSG.Quasithin.MS93.S38G2Main
public import CFSG.Quasithin.MS93.S4A43Main
public import CFSG.Quasithin.MS93.S4AFHolds
public import CFSG.Quasithin.MS93.S4AFcHolds
public import CFSG.Quasithin.MS93.S4A44Main
public import CFSG.Quasithin.MS93.S4A441NoSec
public import CFSG.Quasithin.MS93.S4A441XG
public import CFSG.Quasithin.MS93.S4E
public import CFSG.Quasithin.MS93.S4A442Comm
public import CFSG.Quasithin.MS93.S37RMain
public import CFSG.Quasithin.MS93.S45RF
public import CFSG.Quasithin.MS93.S511SCore
public import CFSG.Quasithin.MS93.S4A44FcWHolds
public import CFSG.Quasithin.MS93.S45Fin
public import CFSG.Quasithin.MS93.S45C14
public import CFSG.Quasithin.MS93.S5A55SpQ
public import CFSG.Quasithin.MS93.S37Main
public import CFSG.Quasithin.MS93.S510Main
public import CFSG.Quasithin.MS93.S59R
public import CFSG.Quasithin.MS93.S5A55Main
public import CFSG.Quasithin.MS93.S5A56Main
public import CFSG.Quasithin.MS93.S5A56F
public import CFSG.Quasithin.MS93.S512ZChain
public import CFSG.Quasithin.MS93.S512FThree
public import CFSG.Quasithin.MS93.Q2GCHolds
public import CFSG.Quasithin.MS93.S45J
public import CFSG.Quasithin.MS93.S5DMain
public import CFSG.Quasithin.MS93.S512GClosed
public import CFSG.Quasithin.MS93.S512HMain
public import CFSG.Quasithin.MS93.S4LCoreDesc
public import CFSG.Quasithin.MS93.S512JHolds
public import CFSG.Quasithin.MS93.S46RMain3
public import CFSG.LieType.Steinberg.CentralExt.F4E8Multiplier
public import CFSG.LieType.Steinberg.CentralExt.PSpMultiplier
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticSmallFieldPerfect
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListAlt7
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Statements
public import CFSG.Quasithin.Background.B15P4LayerDict
public import CFSG.Quasithin.Background.B3ThreeModel
public import CFSG.Quasithin.Background.B3ThreeStruct
public import CFSG.Quasithin.Background.D2Y13
public import CFSG.Quasithin.EmptyFaithful.F918C1
public import CFSG.Quasithin.EmptyFaithful.S14113bMain
public import CFSG.Quasithin.EmptyFaithful.S1417Factor
public import CFSG.Quasithin.MS93.S45B12
public import CFSG.Quasithin.MS93.S45RE
public import CFSG.Quasithin.Vol2.Ch4Sec3C136One
public import CFSG.Quasithin.Vol2.Ch4Sec3L439Mod
public import CFSG.Quasithin.Vol2.Ch5Sec1L34InputsOddAm
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5115
public import CFSG.Quasithin.Vol2.Ch5Sec1Thm5114
public import CFSG.Sporadic.Schreier.J4SNoCompCover
public import CFSG.Walter.Ree.Thompson2.BaseFin
public import CFSG.Walter.ReeOrder.WardLocal
public import CFSG.Walter.W67.Section8.Prop83
public import CFSG.Walter.W67.W2Lemma26A

public section

namespace CFSG.Quasithin.MS93

theorem sqtkQuot_holds :
    SQTKQuot := fun _ _ _ _ _ _ hS f hf hQ =>
  H13.A5.sqtkGroup_of_surjective_quasisimple hS f hf hQ

theorem s43_holds :
    S43 :=
  s43_of_cff (S4A.s4CFF_holds s32_holds) s32_holds

theorem s441_holds
    : S4A.S441 :=
  have hdual := S4A.s441C1Dual_of_s43 s43_holds
  S4A.s441_of hdual
    (S4A.s441End_of s32_holds (S4A.C441.s441C2Cent_of_dual s32_holds s43_holds hdual)
      (S4A.s4CFFcW_holds s32_holds) (S4E.s441EndB_holds s32_holds s43_holds))

theorem s44_frontier
    (h441 : S4A.S441) (h442 : S4A.S442) : S44 :=
  s44_of s32_holds s43_holds h441 h442 (S4A.s4CFFc_holds s32_holds)

theorem s46_frontier
    (hDeg : S46R.S468Deg) : S46 :=
  S46R.s46_of_deg s32_holds (s39_of s32_holds) (s42_of s32_holds) s43_holds ms14AS_holds
    sqtkQuot_holds hDeg

theorem s37_holds
    : S37 :=
  S37.s37_of_qLine (S37L.qLineCase_of S37R.caseIIQ_holds) (s36_of_g2 s38G2_holds)

theorem s512_frontier
    (hL : S512R.Three56ResL) :
    S512 :=
  have hX2 := S33.s33X52_holds
  have hZ := Q2G.q2EvenZ_holds s32_holds
  have hq55 := Q2G.q2Cent55_holds s32_holds
  have hq2c := S5Q2.q2Cent_of_q2CentUC s32_holds (Q2G.q2CentUC_holds s32_holds)
  have h51 := s51_of s32_holds
  have h52 := s52_of S5.s52i_holds
  have h53 := s53_of h51 s32_holds
  have h54 := s54_of h51
  have h55 := s55_of h51 s32_holds hq55 S5.sp4Case55_holds
  have h56 := s56_of h51
  have h58 := S5B.s58_of s32_holds hX2 h52 h54 h55 h56
  have h59 :=
    S5B.s59_of s32_holds hX2 h53 h54 h55 h56 h58 (S59R.open_of s32_holds hX2 h53 h55 h56 h58)
  have h510 := S5B.s510_of s32_holds hX2 h52 h54 h55 h56 h59
    (S5B.s510nxz_of s32_holds hX2 h52 h54 h55 h56 h59 (S5D.s510NXZ'_holds s32_holds))
  have hcore := S511S.s511Core_of s32_holds hX2 h52 h53 h54 (S5.s56f_of h51) hZ h59
  have hn := S5B.s512Nat_holds_of_r2Cent s32_holds (S512N.r2Cent_holds s32_holds)
  have hone := S512Z.oneCF_holds s32_holds hX2 h52 h54 h58 hn s310m_holds
  have hcore2 := S512L.core_holds s32_holds h52 h53 h54 h55 h56
  S512Z.s512_of s32_holds hX2 h52 h54 h55 (S5.s56f_of h51) (S5B.s511_of h510 hcore)
    (S512R.s512TwoF_holds_e s32_holds h52 h54 hZ hq55 hcore2
      (S512G.twoAlt2_closed s32_holds hX2 h52 h54 h55 h56 hq2c))
    (S512R.s512ThreeF_holds s32_holds h54 h58 hone (S512R.threeAlt2_of s32_holds h58
      (S512H.threeAlt2L_holds s32_holds hX2 h52 h54 h58 hq2c))
      (S512R.three56F_of_s51 s32_holds h52 h54 h58 hZ hone hcore2 hL
        (S512F.three56ResA_holds s32_holds hX2 h52 h54)))
    hn s310m_holds

theorem s512_holds :
    S512 :=
  have h51 := s51_of s32_holds
  s512_frontier (S512J.three56ResL_holds s32_holds (s52_of S5.s52i_holds) (s53_of h51 s32_holds)
    (s54_of h51) (s55_of h51 s32_holds (Q2G.q2Cent55_holds s32_holds) S5.sp4Case55_holds) (s56_of h51))

end CFSG.Quasithin.MS93
