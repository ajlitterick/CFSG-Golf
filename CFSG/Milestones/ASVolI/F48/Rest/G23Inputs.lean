module

public import CFSG.Milestones.ASVolI.F48.Rest.G23Data
public import CFSG.Milestones.ASVolI.F48.Rest.PermCheck
public import CFSG.RankThree.PartTwo.Census.Carrier.G2ThreeData
public import Batteries.Data.ByteArray
public import Certificates.Data.CFSGNative.CosetTable.Enum

public section

namespace CFSG.ASVolI

open CFSG.ONSchreier.Native CFSG.Sporadic.HNOddCore CFSG.CosetTable
open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

set_option compiler.extract_closed false

@[expose] def burnsideF48t_g23Mats (_ : Unit := ()) : Array (Array ℕ) :=
  #[CFSG.RankThree.PartTwo.Census.Carrier.G2Three.x0c.toArray,
    CFSG.RankThree.PartTwo.Census.Carrier.G2Three.x1c.toArray,
    CFSG.RankThree.PartTwo.Census.Carrier.G2Three.y0c.toArray,
    CFSG.RankThree.PartTwo.Census.Carrier.G2Three.y1c.toArray]

@[expose] def burnsideF48t_g23Dot (A v : Array ℕ) (i : ℕ) : ℕ :=
  ((List.range 14).map fun k => A[14 * i + k]! * v[k]!).sum

@[expose] def burnsideF48t_g23MulVec (A v : Array ℕ) : Array ℕ :=
  Array.ofFn (n := 14) fun i => burnsideF48t_g23Dot A v i.val % 3

@[expose] def burnsideF48t_g23Norm (v : Array ℕ) : Array ℕ :=
  if v.find? (· != 0) == some 2 then v.map fun x => 2 * x % 3 else v


@[expose] def burnsideF48t_g23Pts (_ : Unit := ()) : Array (Array ℕ) :=
  let b := burnsideF48t_g23PtsStr.toUTF8
  (Array.range 728).map fun k => (Array.range 14).map fun j => b[14 * k + j]!.toNat - 48


@[expose] def burnsideF48t_g23Gens (_ : Unit := ()) : Array (Array ℕ) := burnsideF48t_g23GensArr


@[expose] def burnsideF48t_g23LInv (_ : Unit := ()) : Array (Array ℕ) :=
  burnsideF48t_g23LArr.map (pinvCand 728)

@[expose] def burnsideF48t_g23P1Arr : Array (Array ℕ) :=
  #[burnsideF48t_g23LArr[0]!, burnsideF48t_g23LArr[1]!, burnsideF48t_g23LArr[2]!]

@[expose] def burnsideF48t_g23P2Arr : Array (Array ℕ) :=
  #[burnsideF48t_g23LArr[0]!, burnsideF48t_g23LArr[1]!, burnsideF48t_g23LArr[3]!]

@[expose] def burnsideF48t_g23BArr : Array (Array ℕ) :=
  #[burnsideF48t_g23LArr[0]!, burnsideF48t_g23LArr[1]!]

@[expose] def burnsideF48t_g23S0Arr (_ : Unit := ()) : Array (Array ℕ) :=
  let Li := burnsideF48t_g23LInv ()
  (burnsideF48t_g23SW.map fun w => burnsideF48t_evA 728 burnsideF48t_g23LArr Li w).toArray

@[expose] def burnsideF48t_g23KArr (_ : Unit := ()) : Array (Array ℕ) :=
  let Li := burnsideF48t_g23LInv ()
  (burnsideF48t_g23KW.map fun w => burnsideF48t_evA 728 burnsideF48t_g23LArr Li w).toArray


@[expose] def burnsideF48t_g23ChainS0OK (_ : Unit := ()) : Bool :=
  chainCheck 728 (burnsideF48t_g23S0Arr ()) burnsideF48t_g23WS0 burnsideF48t_g23BaseS0
    burnsideF48t_g23SizesS0

@[expose] def burnsideF48t_g23ChainKOK (_ : Unit := ()) : Bool :=
  chainCheck 728 (burnsideF48t_g23KArr ()) burnsideF48t_g23WK burnsideF48t_g23BaseK
    burnsideF48t_g23SizesK


end CFSG.ASVolI
