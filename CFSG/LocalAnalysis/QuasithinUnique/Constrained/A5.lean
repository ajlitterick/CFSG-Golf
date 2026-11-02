module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Main
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Basic245Proofs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Stage5
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Final
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Stage4
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Stage1
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Stage2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Stage3
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Stage6
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.S2Q
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.S2StageA
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.S2StageB
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.S2StageC
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.S2StageD
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.S2List
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Stage7
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Stage8
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Stage9
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.S9Insp
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Stage10
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3NoProper
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Lemma27A5
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3Main
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCS2Final
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppC56A5

public section

namespace CFSG.QuasithinUnique

open CFSG.QuasithinUnique.A5

theorem lemma2_4_25_of_inputs (hC54s2 : LemmaC54_3_s2) (hC56s2 : LemmaC56_14_s2)
    (h567 : Lemma245_C56_7) (h37 : Vol2Native.A37ForSQTKCat) (h39 : Vol2Native.A39ForSQTKCat)
    (hP1 : CompChi0Block) (hP2 : NoProperA5Block) (hComp : Comp25Component)
    (hlist115 : Lemma115_3_List) (hTab : TabKc3) (hKc3 : Kc3Inspection) : Lemma2_4_25 :=
  lemma2_4_25_of_steps (lemma2_4_25_0_of lemma245_C55 (lemma2_4_25_Q hC54s2 h567))
    (lemma2_4_25_A hC54s2 h567 hC56s2) (lemma2_4_25_B hC54s2 h567 h37 h39 hP1 hP2)
    (lemma2_4_25_C hC54s2 h567 h37 h39 hP1 hP2 hComp (comp25List_of hlist115 hTab))
    (lemma2_4_25_D hKc3)

theorem a5BlockExcluded
    (h246 : Lemma246Chi)
    (h245_4 : Lemma245_4) (hC54 : LemmaC54_3) (h314 : A314A5Excluded)
    (h37 : Vol2Native.A37ForSQTKCat) (h39 : Vol2Native.A39ForSQTKCat)
    (hP1 : CompChi0Block) (hComp : Comp25Component)
    (hlist115 : Lemma115_3_List) (hTab : TabKc3) (hKc3 : Kc3Residual)
    (hSA : ConstrainedSetupAt) (hlin : Lin2BlockExcluded) (ha3 : SingleA3Excluded)
    (hP121 : Id2519.Prop121Three) (h2397 : Lemma2_3_9_7W) : A5BlockExcluded :=
  have h25 : Lemma2_4_25 :=
    lemma2_4_25_of_inputs AppCS2.lemmaC54_3_s2 AppCS2.lemmaC56_14_s2
      (lemma245_C56_7 AppC.c56A5Case AppCS2.c56DoubleCase) h37 h39 hP1 G3.noProperA5Block hComp
      hlist115 hTab
      (kc3Inspection_of_residual hKc3)
  have h247 : DoubleA3.Lemma2_4_27 := DoubleA3.lemma2_4_27_of hSA hlin ha3 h25
  a5BlockExcluded_of_steps h25
    (lemma2_4_29_1 h247 h245_4 hC54 h314) (lemma2_4_29_2 h247 h245_4 hC54 h314)
    (lemma2_4_29_3 h247 h245_4 hC54 h314) (lemma2_4_29_4 h247 h245_4 hC54 h314)
    (lemma2_4_29_5 h247 h246) (lemma2_4_29_6 h247 h245_4 hC54 h314)
    (lemma2_4_29_7 h247 h245_4 hC54 h314)
    (lemma2_4_29_8 h247 h245_4 hC54 h314 h25 hSA hlin ha3)
    (lemma2_4_29_9 h247 h245_4 hC54 h314 hP121 h2397
      (lemma2_4_29_9_K_proved h247 h245_4 hC54 h314 hP121)) (lemma2_4_29_10 h247 h245_4 hC54 h314)
    lemma2_4_29_11

end CFSG.QuasithinUnique
