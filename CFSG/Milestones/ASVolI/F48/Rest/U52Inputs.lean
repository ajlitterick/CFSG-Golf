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

@[expose] def burnsideF48t_u52Dot (a b : Array ℕ) : ℕ :=
  burnsideF48t_gf4Mul a[0]! b[0]! ^^^ burnsideF48t_gf4Mul a[1]! b[1]! ^^^
    burnsideF48t_gf4Mul a[2]! b[2]! ^^^ burnsideF48t_gf4Mul a[3]! b[3]! ^^^
    burnsideF48t_gf4Mul a[4]! b[4]!

@[expose] def burnsideF48t_u52Bar (a : Array ℕ) : Array ℕ :=
  Array.ofFn (n := 5) fun i => burnsideF48t_gf4Sq a[i.val]!

@[expose] def burnsideF48t_u52TV (u v : Array ℕ) : Array ℕ :=
  let s := burnsideF48t_u52Dot (burnsideF48t_u52Bar u) v
  Array.ofFn (n := 5) fun i => v[i.val]! ^^^ burnsideF48t_gf4Mul u[i.val]! s

@[expose] def burnsideF48t_u52Gens (_ : Unit := ()) : Array (Array ℕ) := burnsideF48t_u52GensArr

@[expose] def burnsideF48t_u52GensInv (_ : Unit := ()) : Array (Array ℕ) :=
  (burnsideF48t_u52Gens ()).map (pinvCand 462)

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

@[expose] def burnsideF48t_u52KL (_ : Unit := ()) : List (Array ℕ) :=
  let Li := burnsideF48t_u52LInv ()
  burnsideF48t_u52KW.map fun w => burnsideF48t_evA 462 burnsideF48t_u52LArr Li w

@[expose] def burnsideF48t_u52LevX (_ : Unit := ()) : Array Level :=
  burnsideF48t_levels 462 (burnsideF48t_u52Gens ()) burnsideF48t_u52WX burnsideF48t_u52BaseX

@[expose] def burnsideF48t_u52LevS0 (_ : Unit := ()) : Array Level :=
  burnsideF48t_levels 462 (burnsideF48t_u52S0Arr ()) burnsideF48t_u52WS0 burnsideF48t_u52BaseS0

@[expose] def burnsideF48t_u52ChainXOK (_ : Unit := ()) : Bool :=
  chainCheck 462 (burnsideF48t_u52Gens ()) burnsideF48t_u52WX burnsideF48t_u52BaseX
    burnsideF48t_u52SizesX

@[expose] def burnsideF48t_u52ChainP1OK (_ : Unit := ()) : Bool :=
  chainCheck 462 burnsideF48t_u52P1Arr burnsideF48t_u52WP1 burnsideF48t_u52BaseP1
    burnsideF48t_u52SizesP1

@[expose] def burnsideF48t_u52ChainP2OK (_ : Unit := ()) : Bool :=
  chainCheck 462 burnsideF48t_u52P2Arr burnsideF48t_u52WP2 burnsideF48t_u52BaseP2
    burnsideF48t_u52SizesP2

@[expose] def burnsideF48t_u52ChainBOK (_ : Unit := ()) : Bool :=
  chainCheck 462 burnsideF48t_u52BArr burnsideF48t_u52WB burnsideF48t_u52BaseB
    burnsideF48t_u52SizesB

@[expose] def burnsideF48t_u52ChainS0OK (_ : Unit := ()) : Bool :=
  chainCheck 462 (burnsideF48t_u52S0Arr ()) burnsideF48t_u52WS0 burnsideF48t_u52BaseS0
    burnsideF48t_u52SizesS0

@[expose] def burnsideF48t_u52ChainKOK (_ : Unit := ()) : Bool :=
  chainCheck 462 (burnsideF48t_u52KArr ()) burnsideF48t_u52WK burnsideF48t_u52BaseK
    burnsideF48t_u52SizesK


@[expose] def burnsideF48t_u52HArr (H : List (List (Fin 6 × Bool))) : Array (Array ℕ) :=
  let G := burnsideF48t_u52Gens ()
  let Gi := G.map (pinvCand 462)
  (H.map fun w => burnsideF48t_evA 462 G Gi w).toArray


@[expose] def burnsideF48t_u52S0NormOK (_ : Unit := ()) : Bool :=
  let L := burnsideF48t_u52LArr
  let Li := burnsideF48t_u52LInv ()
  let S0 := burnsideF48t_u52S0Arr ()
  let lvS := burnsideF48t_u52LevS0 ()
  allBelowN 2 fun i => S0.all fun s =>
    burnsideF48t_sift 462 lvS burnsideF48t_u52BaseS0 (pcomp 462 (pcomp 462 L[i]! s) Li[i]!)


abbrev burnsideF48t_u52Ws (i j k : ℕ) : List (List (Fin 4 × Bool)) :=
  burnsideF48s_eWs burnsideF48t_u52R1 burnsideF48t_u52R2 4 (burnsideF48t_u52XW.getD i [])
    (burnsideF48t_u52YW.getD j []) (burnsideF48t_u52KW.getD k [])

abbrev burnsideF48t_u52WsB : List (List (Fin (subsetOf 4 [0, 1, 2]).length × Bool)) :=
  restrictWords (subsetOf 4 [0, 1, 2]) (burnsideF48t_u52R1 ++ burnsideF48t_u52R2)


end CFSG.ASVolI
