
module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCo3Base

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCo3Check
public meta import CFSG.Sporadic.Schreier.Co3Cert
public meta import Certificates.Data.CFSGNative.Schreier.Check
public meta import CFSG.Sporadic.Schreier.Co3SylowCheck
public meta import Certificates.Data.CFSGNative.Schreier.SetOrbit
public meta import CFSG.Sporadic.Schreier.Co3FaithfulData
public meta import Certificates.Data.CFSGNative.Co3.Data
public meta import CFSG.Sporadic.Schreier.Co3CentralizerCheck
public meta import CFSG.Sporadic.Schreier.Co3Sp6Check
public meta import CFSG.Sporadic.Schreier.Co3SecondCheck
public meta import CFSG.Sporadic.Schreier.M12Data
public meta import CFSG.Sporadic.Schreier.CountSpec
public meta import Certificates.Data.CFSGNative.SporadicSchreier.Count
public meta import CFSG.Sporadic.Schreier.Co3StabItInputs
public meta import Certificates.Data.CFSGNative.Co3Schreier.Orbit
public meta import CFSG.Sporadic.Mathieu.M12
public meta import CFSG.Monster.B.Mathieu.Order
public meta import CFSG.Sporadic.Schreier.Co3GenerationCheck
public meta import CFSG.Sporadic.Schreier.Co3Outer
public meta import Mathlib.Data.Matrix.Block
public meta import CFSG.Sporadic.Schreier.Co3OrderCheck
public meta import CFSG.Sporadic.Schreier.MathieuSylowAutMain
public meta import CFSG.Sporadic.Schreier.M12
public meta import CFSG.Sporadic.Schreier.M12Pinned
public meta import Certificates.Data.CFSGNative.SporadicSchreier.MathieuOddCore

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.Co3

open Subgroup CFSG.Open CFSG.ComponentClassification.RankTwoSporadic
open CFSG.ComponentClassification.RankTwoSporadic.Cert CFSG.Sporadic.Schreier.Co3
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native

theorem co3_yCensus : YCensus (co3P.subgroupOf co3P) (fun _ => False) := by
  obtain ⟨inX, inW, d, hX, hW, hc, hgen, hlen⟩ := co3_check
  have hN : (co3P.subgroupOf co3P).Normal := by
    rw [subgroupOf_self]
    infer_instance
  exact yCensus_pair_conjW_of (m := 484147125) le_rfl hN co3PS_lt co3InP_iff rep_idA
    (one_mem _) hX hW hc hgen (by rw [hlen]; norm_num [card_co3P]) (by decide)

theorem sporadicCaseOdd_Co3 (h32 : AS76b.Lemma32) (h33 : AS76b.Lemma33Three) :
    SporadicCaseOdd .Co3 :=
  sporadicCaseOdd_of_yCensus h32 h33 co3AutModel co3_yCensus

end CFSG.ComponentClassification.RankTwoSporadic.Co3
