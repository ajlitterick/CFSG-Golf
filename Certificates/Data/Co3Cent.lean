module

public import Certificates.Data.K426Checks
public import Certificates.Data.Co3Pump
public import CFSG.RankThree.PartOne.KS.PKitLeaf
public import Certificates.Data.L28Presentation
public meta import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3ThreeInputs
public meta import Certificates.Data.K426Checks
public meta import Certificates.Data.Co3Pump
public meta import CFSG.RankThree.PartOne.KS.PKitLeaf
public meta import Certificates.Data.L28Presentation

public section

namespace CFSG.HardMathSupport.Dickson.I271.Co3Cent

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Monster.B.Mathieu
  CFSG.Monster.B.Fischer CFSG.RankThree.Native CFSG.RankThree.PartOne
  CFSG.RankThree.PartTwo.KFacts.K426 CFSG.Sporadic.Schreier.Co3
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3T
  CFSG.HardMathSupport.Solomon.Coordinator.Co3Pump
  CFSG.HardMathSupport.Dickson.I271.L28Presentation

@[expose] def hex : String := include_str "Co3Cent.txt"

@[expose] def arr (k : ℕ) : Array ℕ := hexTable 3 276 (276 * k) hex


@[expose] def rGens (_ : Unit := ()) : Array (Array ℕ) :=
  Array.ofFn fun j : Fin 5 => arr (31 + j.val)

@[expose] def lGens (_ : Unit := ()) : Array (Array ℕ) :=
  Array.ofFn fun j : Fin 2 => arr (36 + j.val)


@[expose] def dCert (_ : Unit := ()) : ArrCert := enumBfs 276 (dGens ()) keys 250


@[expose] def lCert (_ : Unit := ()) : ArrCert := enumBfs 276 (lGens ()) keys 520


end CFSG.HardMathSupport.Dickson.I271.Co3Cent
