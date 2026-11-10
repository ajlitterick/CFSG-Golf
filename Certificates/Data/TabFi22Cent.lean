module

public import Certificates.Data.K426Checks
public import CFSG.Monster.B.Fischer.Fi22OrderCheckInputs
public meta import Certificates.Data.K426Checks
public meta import CFSG.Monster.B.Fischer.PinnedChainInputs
public meta import CFSG.Monster.B.Fischer.Fi22OrderCheckInputs
public meta import CFSG.RankThree.PartOne.KS.PKit

public section

namespace CFSG.HardMathSupport.Dickson.I271.TabFi22Cent

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Monster.B.Fischer
  CFSG.Monster.B.Mathieu CFSG.RankThree.Native CFSG.RankThree.PartOne
  CFSG.RankThree.PartTwo.KFacts.K426

@[expose] def hex : String := include_str "TabFi22Cent.txt"

@[expose] def arr (k : ℕ) : Array ℕ := hexTable 3 3510 (3510 * k) hex

@[expose] def dArr (_ : Unit := ()) : Array ℕ := arr 0

@[expose] def xArr (_ : Unit := ()) : Array ℕ := arr 1

@[expose] def lArrs (_ : Unit := ()) : Array (Array ℕ) :=
  Array.ofFn fun j : Fin 8 => arr (2 + j.val)

@[expose] def lWords : Array (List ℤ) :=
  #[[], [], [-1, -2, -2, 1], [-1, -3, 1, 2], [-1, -2, -1, 2, -3, 2, 3, 1], [3, -4, 5, 5, 3],
    [5, 6, -5], [-3, -6, 5, 4, 3, 4]]


@[expose] def relsU43 : List (List (Fin 2 × Bool)) :=
  [[(0, true), (0, true)], [(1, true), (1, true), (1, true), (1, true), (1, true), (1, true)],
      [(0, true), (1, false), (0, true), (1, false), (0, true), (1, false), (0, true), (1, false),
      (0, true), (1, false), (0, true), (1, false), (0, true), (1, false)],[(0, true), (1, true),
      (1, true), (0, true), (1, false), (1, false), (0, true), (1, false), (1, false), (0, true),
      (1, false), (1, false), (0, true), (1, true), (1, true), (0, true), (1, true), (1, true)],
      [(1, true), (0, true), (1, true), (1, true), (1, true), (0, true), (1, false), (1, false),
      (1, false), (0, true), (1, false), (1, false), (1, false), (0, true), (1, false), (1, false),
      (1, false), (0, true), (1, true), (1, true)],[(0, true), (1, false), (1, false), (0, true),
      (1, true), (0, true), (1, false), (1, false), (0, true), (1, false), (0, true), (1, true),
      (1, true), (0, true), (1, true), (0, true), (1, false), (1, false), (0, true), (1, false),
      (0, true), (1, false), (1, false), (0, true), (1, true), (0, true), (1, true), (1, true),
      (0, true), (1, false)],[(0, true), (1, true), (0, true), (1, true), (0, true), (1, true),
      (1, true), (1, true), (0, true), (1, false), (0, true), (1, false), (1, false), (0, true),
      (1, false), (0, true), (1, false), (1, false), (0, true), (1, false), (0, true), (1, false),
      (0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, false), (0, true),
      (1, true), (1, true), (0, true), (1, false), (1, false), (1, false), (0, true), (1, true),
      (1, true), (0, true), (1, false), (0, true), (1, false), (1, false), (0, true), (1, false),
      (1, false)]]


end CFSG.HardMathSupport.Dickson.I271.TabFi22Cent
