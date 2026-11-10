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

@[expose] def burnsideF48t_u52eInvOK (_ : Unit := ()) : Bool :=
  let L := burnsideF48t_u52eLArr ()
  let Li := burnsideF48t_u52eLInv ()
  L.size == 5 && Li.size == 5 && allBelowN 5 fun i => pisInv 462 L[i]! Li[i]!

@[expose] def burnsideF48t_u52eFOK (_ : Unit := ()) : Bool :=
  let F := burnsideF48t_u52eF
  let lv := burnsideF48t_u52LevX ()
  let G := burnsideF48t_u52Gens ()
  pisInv 462 F F && F[0]! == 0 && F[165]! == 165 &&
    (G.all fun g => burnsideF48t_sift 462 lv burnsideF48t_u52BaseX (pcomp 462 (pcomp 462 F g) F)) &&
    !burnsideF48t_sift 462 lv burnsideF48t_u52BaseX F

@[expose] def burnsideF48t_u52eRelOK (_ : Unit := ()) : Bool :=
  let L := burnsideF48t_u52eLArr ()
  let Li := burnsideF48t_u52eLInv ()
  (burnsideF48t_u52eR1 ++ burnsideF48t_u52eR2).all
    fun r => peq 462 (burnsideF48t_evA 462 L Li r) (pid 462)

@[expose] def burnsideF48t_u52eKL (j : ℕ) (_ : Unit := ()) : List (Array ℕ) :=
  let L := burnsideF48t_u52eLArr ()
  let Li := burnsideF48t_u52eLInv ()
  (burnsideF48t_u52eKhW.getD j []).map fun w => burnsideF48t_evA 462 L Li w

@[expose] def burnsideF48t_u52eKG (j : ℕ) (_ : Unit := ()) : Array (Array ℕ) :=
  let KL := burnsideF48t_u52eKL j ()
  #[KL.getD 1 (pid 462), KL.getD 3 (pid 462), KL.getD 9 (pid 462)]

@[expose] def burnsideF48t_u52eKhOK (_ : Unit := ()) : Bool :=
  let KL := burnsideF48t_u52KL ()
  burnsideF48t_u52eKhW.length == 4 &&
    allBelowN 4 fun j =>
      let C := burnsideF48t_u52eKL j ()
      C.length == 18 && burnsideF48t_closedL 462 (burnsideF48t_u52eKG j ()) C &&
        peq 462 (C.getD 1 (pid 462)) (KL.getD 1 (pid 462)) &&
        peq 462 (C.getD 3 (pid 462)) (KL.getD 3 (pid 462)) && !KL.contains (C.getD 9 (pid 462))


@[expose] def burnsideF48t_u52eCandOK (_ : Unit := ()) : Bool :=
  let L := burnsideF48t_u52eLArr ()
  let Li := burnsideF48t_u52eLInv ()
  let KW := burnsideF48t_u52eKhW.getD 2 []
  allBelowN 4 fun i => allBelowN 2 fun j => allBelowN 18 fun k =>
    match burnsideF48t_u52eCands.find? (fun t => t.1 == i && t.2.1 == j && t.2.2.1 == k) with
    | some t => t.2.2.2 != 165 || peq 462 (burnsideF48t_evA 462 L Li
        (burnsideF48s_eCandRel 4 (burnsideF48t_u52eXW.getD i []) (burnsideF48t_u52eYW.getD j [])
          (KW.getD k []))) (pid 462)
    | none =>
      let u := burnsideF48t_evA 462 L Li (burnsideF48t_u52eXW.getD i [])
      let v := burnsideF48t_evA 462 L Li (burnsideF48t_u52eYW.getD j [])
      let c := burnsideF48t_evA 462 L Li (KW.getD k [])
      !peq 462 (pcomp 462 (pcomp 462 u v) c) (pcomp 462 c (pcomp 462 u v))

abbrev burnsideF48t_u52eWs (i j k : ℕ) : List (List (Fin 5 × Bool)) :=
  burnsideF48s_eWs burnsideF48t_u52eR1 burnsideF48t_u52eR2 4 (burnsideF48t_u52eXW.getD i [])
    (burnsideF48t_u52eYW.getD j []) ((burnsideF48t_u52eKhW.getD 2 []).getD k [])

abbrev burnsideF48t_u52eWsB : List (List (Fin (subsetOf 5 [0, 1, 2, 4]).length × Bool)) :=
  restrictWords (subsetOf 5 [0, 1, 2, 4]) (burnsideF48t_u52eR1 ++ burnsideF48t_u52eR2)


end CFSG.ASVolI
