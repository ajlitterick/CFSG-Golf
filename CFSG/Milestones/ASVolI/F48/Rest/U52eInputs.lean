module

public import CFSG.Milestones.ASVolI.F48.Rest.U52eData
public import CFSG.Milestones.ASVolI.F48.Rest.U52Inputs

public section

namespace CFSG.ASVolI

open CFSG.ONSchreier.Native CFSG.Sporadic.HNOddCore CFSG.CosetTable
open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

set_option compiler.extract_closed false

@[expose] def burnsideF48t_u52eLArr (_ : Unit := ()) : Array (Array ℕ) :=
  burnsideF48t_u52LArr.push burnsideF48t_u52eF

@[expose] def burnsideF48t_u52eLInv (_ : Unit := ()) : Array (Array ℕ) :=
  (burnsideF48t_u52eLArr ()).map (pinvCand 462)


abbrev burnsideF48t_u52eWs (i j k : ℕ) : List (List (Fin 5 × Bool)) :=
  burnsideF48s_eWs burnsideF48t_u52eR1 burnsideF48t_u52eR2 4 (burnsideF48t_u52eXW.getD i [])
    (burnsideF48t_u52eYW.getD j []) ((burnsideF48t_u52eKhW.getD 2 []).getD k [])

abbrev burnsideF48t_u52eWsB : List (List (Fin (subsetOf 5 [0, 1, 2, 4]).length × Bool)) :=
  restrictWords (subsetOf 5 [0, 1, 2, 4]) (burnsideF48t_u52eR1 ++ burnsideF48t_u52eR2)


end CFSG.ASVolI
