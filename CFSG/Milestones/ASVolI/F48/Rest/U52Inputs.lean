module

public import CFSG.Milestones.ASVolI.F48.Rest.U52Data
public import CFSG.Milestones.ASVolI.F48.Rest.PermCheck
public import CFSG.Milestones.ASVolI.F48.Small.EngCheck
public import CFSG.Milestones.ASVolI.F48.Rest.GF4
public import CFSG.Certificates.CosetTablePresented

public section

namespace CFSG.ASVolI

open CFSG.ONSchreier.Native CFSG.Sporadic.HNOddCore CFSG.CosetTable
open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

set_option compiler.extract_closed false


@[expose] def burnsideF48t_u52Gens (_ : Unit := ()) : Array (Array ℕ) := burnsideF48t_u52GensArr


@[expose] def burnsideF48t_u52LInv (_ : Unit := ()) : Array (Array ℕ) :=
  burnsideF48t_u52LArr.map (pinvCand 462)


@[expose] def burnsideF48t_u52P1Arr : Array (Array ℕ) :=
  #[burnsideF48t_u52LArr[0]!, burnsideF48t_u52LArr[1]!, burnsideF48t_u52LArr[2]!]

@[expose] def burnsideF48t_u52P2Arr : Array (Array ℕ) :=
  #[burnsideF48t_u52LArr[0]!, burnsideF48t_u52LArr[1]!, burnsideF48t_u52LArr[3]!]

@[expose] def burnsideF48t_u52BArr : Array (Array ℕ) :=
  #[burnsideF48t_u52LArr[0]!, burnsideF48t_u52LArr[1]!]

@[expose] def burnsideF48t_u52S0Arr (_ : Unit := ()) : Array (Array ℕ) :=
  let Li := burnsideF48t_u52LInv ()
  (burnsideF48t_u52SW.map fun w => burnsideF48t_evA 462 burnsideF48t_u52LArr Li w).toArray

@[expose] def burnsideF48t_u52KArr (_ : Unit := ()) : Array (Array ℕ) :=
  let Li := burnsideF48t_u52LInv ()
  (burnsideF48t_u52KGenIdx.map fun i =>
    burnsideF48t_evA 462 burnsideF48t_u52LArr Li (burnsideF48t_u52KW.getD i [])).toArray


abbrev burnsideF48t_u52Ws (i j k : ℕ) : List (List (Fin 4 × Bool)) :=
  burnsideF48s_eWs burnsideF48t_u52R1 burnsideF48t_u52R2 4 (burnsideF48t_u52XW.getD i [])
    (burnsideF48t_u52YW.getD j []) (burnsideF48t_u52KW.getD k [])

abbrev burnsideF48t_u52WsB : List (List (Fin (subsetOf 4 [0, 1, 2]).length × Bool)) :=
  restrictWords (subsetOf 4 [0, 1, 2]) (burnsideF48t_u52R1 ++ burnsideF48t_u52R2)


end CFSG.ASVolI
