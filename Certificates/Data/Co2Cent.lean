module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co2ThreeInputs
public import Certificates.Data.K426Checks
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo2Kit
public import Certificates.Data.U42Presentation
public meta import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co2ThreeInputs
public meta import Certificates.Data.K426Checks
public meta import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo2Kit
public meta import Certificates.Data.U42Presentation

public section

namespace CFSG.HardMathSupport.Dickson.I271.Co2Cent

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Monster.B.Mathieu
  CFSG.Monster.B.Fischer CFSG.RankThree.Native CFSG.RankThree.PartOne CFSG.Sporadic.Co2Cert
  CFSG.RankThree.PartTwo.KFacts.K426 CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co2T
  CFSG.HardMathSupport.Dickson.I271 CFSG.HardMathSupport.Dickson.I271.U42Presentation

@[expose] def co2Hex : String := include_str "Co2Cent.txt"

@[expose] def co2Arr (k : ℕ) : Array ℕ := hexTable 3 2300 (2300 * k) co2Hex


@[expose] def co2ChainAWords : Array (List ℤ) :=
  #[[], [], [2, 1, 2], [-1, -3], [-1, -4, -4, -3, 4, 1], [-5, -4, -5, 4, 4, 5, -4, -4, 5, 4], [4, 4, -5, 6, -4, -4], [4, 4, 7, -4, -4], [4, 4, 8, -4, -4], [-7, -6, -8, 9, 6, 7], [-6, 10, 6], [-7, -6, -4, -5, -8, 11, 5, 4], [-4, -4, -6, 4, 9, 4], [-5, -7, -11, -13, -4, -5, -4, 8, -12, 4], [-5, -8, -9, -12, -13, -4, -9, -5, 13, 6, -4], [-13, 15, 13]]


@[expose] def co2RGens (_ : Unit := ()) : Array (Array ℕ) :=
  Array.ofFn fun j : Fin 4 => co2Arr (33 + j.val)


@[expose] def co2ChainBWords : Array (List ℤ) :=
  #[[], [], [2, 1, 2], [-1, -3], [-1, -4, -4, -3, 4, 1], [4, 5, -4], [-4, -5, 6, 5, 4], [-4, 7, 4], [-6, 8, 6], [-7, 9, 7], [-5, 4, 9, -4, 5], [-4, -8, 11, 8, 4], [-6, -10, 12, 10, 6], [-6, -11, -7, 12, 7, 11, 6], [-4, 12, 4], [-6, 15, 6], [-12, -14, -5, -9, -4, -4, 11, -4]]


@[expose] def co2LArrs (_ : Unit := ()) : Array (Array ℕ) :=
  Array.ofFn fun j : Fin 6 => co2Arr (37 + j.val)

@[expose] def co2LGens (_ : Unit := ()) : Array (Array ℕ) :=
  Array.ofFn fun j : Fin 2 => co2Arr (37 + j.val)

@[expose] def co2LWords : Array (List ℤ) :=
  #[[], [], [-2, 1, 2], [2, -1, -2, -2], [-3, -4, -3, 4, -3, -4, -1, -2, 3, 2, 1], [-3, -4, -4, -5, 4, 3, 4, 4]]

@[expose] def co2LBase : Array ℕ :=
  [0, 2, 3].toArray


end CFSG.HardMathSupport.Dickson.I271.Co2Cent
