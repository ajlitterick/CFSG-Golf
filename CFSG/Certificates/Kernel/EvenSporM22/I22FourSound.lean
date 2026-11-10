module

public import Certificates.Data.Kernel.EvenSporM22.I22FourDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.I22Four

import CFSG.Certificates.Kernel.Spor.RelTR
import CFSG.Certificates.Kernel.Enum.ZCSound
import CFSG.Certificates.Kernel.LocalQTCovPerm
import CFSG.Certificates.Kernel.LocalQTCovParse
import CFSG.Certificates.Kernel.LocalQTCovEqns
public import CFSG.Certificates.Kernel.LocalQTPermSound
import CFSG.Certificates.Kernel.SporSch.LyTxtLemmas
import CFSG.Certificates.Kernel.Spor.DecLinesRead

namespace CFSG.KC.I22F.Pf

open CFSG.KC.DecText CFSG.KS.DecLines CFSG.KS.SporSch.LyTxt


open CFSG.KC.Enum CFSG.KS CFSG.KS.TW CFSG.KS.RelTR CFSG.Sporadic.Th.Native CFSG.KC.LQT.Syl

noncomputable abbrev pp (P i : Nat) : Nat := pg 15 32767 P i


variable {n : Nat} {F : Nat × Bool → Nat → Nat}


variable {A AI B BI : Nat}


noncomputable def xL (A AI B BI : Nat) (sA sB : List (Nat × Bool)) (L : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun p => p)
    (fun l _ ih p => strictN (ih p) (fun q => nIf(Nat.beq l (nat_lit 0), wimg A AI B BI sA q,
      wimg A AI B BI sB q))) L


end CFSG.KC.I22F.Pf

public section

namespace CFSG.KC.I22F

open CFSG.KC.I22F.Pf CFSG.KC.Enum CFSG.KC.DecText CFSG.KS CFSG.KS.TW CFSG.KS.RelTR
  CFSG.Sporadic.Th.Native CFSG.Sporadic.Bridge.TwoGen.Native CFSG.EvenSporadicStandard.M22Std
  CFSG.QuasithinUnique.Ch1.M22Cover CFSG.KC.LQT.Cov CFSG.KC.LQT.Syl CFSG.KC.M22S
  CFSG.Sporadic.Recognition.M22Multiplier CFSG.Sporadic.Recognition.CoverRecipe
  CFSG.LieType.Multipliers


end CFSG.KC.I22F

end
