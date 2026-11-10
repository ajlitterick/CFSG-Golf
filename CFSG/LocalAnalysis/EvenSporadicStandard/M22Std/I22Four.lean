module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.I22Check
public import CFSG.Sporadic.Recognition.M22MultiplierInputs

public section

namespace CFSG.EvenSporadicStandard.M22Std

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Bridge.TwoGen
  CFSG.Sporadic.Recognition.M22Multiplier CFSG.Sporadic.Recognition.CoverRecipe
  CFSG.LieType.Multipliers CFSG.QuasithinUnique.Ch1.M22Cover
open CFSG.Monster.B CFSG.Monster.B.Co2.Native
open CFSG.Monster.B.Co2 (rep_compA rep_idA eqA_iff eq_of_eqA)
open CFSG.Sporadic.Bridge.TwoGen.Native (relCheck wordTab letterTab)
open CFSG.Sporadic.Schreier.Tits (getElem!_ofFn_of_lt)

@[expose] def i22fParse (s : String) : Table :=
  (((s.splitOn " ").filterMap String.toNat?).map UInt32.ofNat).toArray

@[expose] def i22fAlphaText : String := include_str "I22FourAlpha.txt"

@[expose] def i22fBetaText : String := include_str "I22FourBeta.txt"


@[expose] def i22fAlpha (_ : Unit := ()) : Table := i22fParse i22fAlphaText

@[expose] def i22fBeta (_ : Unit := ()) : Table := i22fParse i22fBetaText


section Sound


end Sound


end CFSG.EvenSporadicStandard.M22Std
