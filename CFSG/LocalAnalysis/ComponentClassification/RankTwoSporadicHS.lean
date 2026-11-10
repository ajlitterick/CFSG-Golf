
module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicHSBase

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicHSCheck
public meta import CFSG.Sporadic.Schreier.PairHSCert
public meta import Certificates.Data.CFSGNative.PairSchreier.Core
public meta import Certificates.Data.CFSGNative.Schreier.Check
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public meta import CFSG.Sporadic.Schreier.PairMcLCert
public meta import CFSG.Sporadic.Schreier.PairMcLCheck
public meta import Certificates.Data.CFSGNative.PairSchreier.Counts
public meta import CFSG.Sporadic.Schreier.PairHSCheck
public meta import CFSG.Sporadic.SmallOddCore.McLData
public meta import CFSG.Sporadic.SmallOddCore.McLWords
public meta import CFSG.Sporadic.Schreier.PairF2Sep
public meta import Certificates.Data.CFSGNative.HS.Data
public meta import Certificates.Data.CFSGNative.HS.SmallF2

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.HS

open Subgroup CFSG.Open CFSG.ComponentClassification.RankTwoSporadic
open CFSG.ComponentClassification.RankTwoSporadic.Cert CFSG.RankThree.Native
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native

theorem hs_yCensus : YCensus (hs100P.subgroupOf hs100R) (fun _ => False) := by
  obtain ⟨inX, inW, d, hX, hW, hc, hgen, hlen⟩ := hs_check
  exact yCensus_pair_conjW_of (m := 86625) hs100P_le_R hs100P_normal_R hsPS_lt hsInP_iff
    rep_hs100U hs100U_mem_R hX hW hc hgen (by rw [hlen]; norm_num [card_hs100R]) (by decide)

theorem sporadicCaseOdd_HS (h32 : AS76b.Lemma32) (h33 : AS76b.Lemma33Three) :
    SporadicCaseOdd .HS :=
  sporadicCaseOdd_of_yCensus h32 h33 hsAutModel hs_yCensus

end CFSG.ComponentClassification.RankTwoSporadic.HS
