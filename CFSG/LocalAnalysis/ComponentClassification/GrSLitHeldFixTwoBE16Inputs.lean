module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldFixTwoBCheckInputs
public import CFSG.Assembly.LowTwoRankDefs

public noncomputable section

namespace CFSG.ComponentClassification.GrSLit.HeldFix

open CFSG.ComponentClassification.PSL3Four CFSG.PSL3Four.Native CFSG.Sporadic.HeldB CFSG.Sporadic.SmallOddCore
open CFSG.Monster.B.Co2.Native CFSG.Certificates

@[expose] def heU1Tabs (_ : Unit := ()) : Array Tab := Array.ofFn (n := 3) fun i => heRGens[i.val]!

@[expose] def heU2Tabs (_ : Unit := ()) : Array Tab := Array.ofFn (n := 3) fun i => heRGens[i.val + 3]!


@[expose] def heLiftTab (i : Nat) : Tab := hfCTab (heRWords.getD i [])


end CFSG.ComponentClassification.GrSLit.HeldFix
