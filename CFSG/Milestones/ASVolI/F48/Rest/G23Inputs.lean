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


@[expose] def burnsideF48t_g23Gens (_ : Unit := ()) : Array (Array ℕ) := burnsideF48t_g23GensArr


@[expose] def burnsideF48t_g23LInv (_ : Unit := ()) : Array (Array ℕ) :=
  burnsideF48t_g23LArr.map (pinvCand 728)


@[expose] def burnsideF48t_g23S0Arr (_ : Unit := ()) : Array (Array ℕ) :=
  let Li := burnsideF48t_g23LInv ()
  (burnsideF48t_g23SW.map fun w => burnsideF48t_evA 728 burnsideF48t_g23LArr Li w).toArray

@[expose] def burnsideF48t_g23KArr (_ : Unit := ()) : Array (Array ℕ) :=
  let Li := burnsideF48t_g23LInv ()
  (burnsideF48t_g23KW.map fun w => burnsideF48t_evA 728 burnsideF48t_g23LArr Li w).toArray


end CFSG.ASVolI
