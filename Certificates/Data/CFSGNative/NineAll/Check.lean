module

public import Certificates.Data.CFSGNative.ReflExt.Check
public import Certificates.Data.CFSGNative.TwoNodeSmall.Check

public section

namespace CFSG.NineAll

open CFSG.TwoNodeSmall CFSG.ReflExt

set_option compiler.extract_closed false

@[expose, reducible] def withBound (P : Pt) (b : Nat) : Pt := { P with bound := b }

@[expose] def isBadW : Witness → Bool
  | .transv _ => true
  | .order _ => true
  | _ => false

@[expose] def verifyBad (P : Pt) (w : Witness) : Bool := isBadW w && verify P w

structure Rep0 where
  r : Refl
  w : Witness

structure Rep2 where
  r : Refl
  w : Witness

inductive NKind
  | w (w : Witness)
  | cent

structure NRep where
  r : Refl
  kind : NKind
  roots : List Root
  reps2 : List Rep2
  orb2 : List OEnt

structure NTables where
  roots : List Root
  orb0 : List OEnt
  reps0 : List Rep0
  orb1 : List OEnt
  reps : List NRep


@[expose] def centOK (P0 : Pt) (t : Refl) : Bool :=
  P0.gens.all fun g =>
    (List.range P0.D).all fun j =>
      P0.vecEq (P0.applyRefl g (P0.applyRefl t (P0.unit j))) (P0.applyRefl t (P0.applyRefl g (P0.unit j)))

@[expose] def centRootsOK (P0 : Pt) (t : Refl) (roots : List Root) : Bool :=
  roots.all fun ρ => reqb ρ.r t || reqb ρ.r (negR P0 t) || P0.dotv ρ.r.f P0.x == 0


@[expose] def vFixN (P0 : Pt) : Bool := P0.gens.all fun g => P0.dotv g.f P0.x == 0

@[expose] def vRootsN (P0 : Pt) (T : NTables) : Bool :=
  T.roots.all fun ρ => wfR P0 ρ.r && realizes P0 ρ.w ρ.r && P0.dotv ρ.r.f P0.x == 0

@[expose] def candOfN (P0 : Pt) (T : NTables) : List Refl := candList P0 (T.roots.map (·.r))

@[expose] def vCover0 (P0 : Pt) (T : NTables) (cand : List Refl) : Bool :=
  (cand.filter fun c => P0.dotv c.f P0.x == 0).all fun c =>
    (T.roots.any fun ρ => reqb ρ.r c) || T.orb0.any fun e => reqb e.e c

@[expose] def entry0OK (P0 : Pt) (T : NTables) (e : OEnt) : Bool :=
  wfR P0 e.e && decide (e.j < T.reps0.length) &&
    (match T.reps0[e.j]? with
     | some rp => realizes (withExtra P0 [e.e]) (e.w ++ [P0.gens.length] ++ e.w.reverse) rp.r
     | none => false)

@[expose] def rep0OK (P0 : Pt) (Bstab : Nat) (rp : Rep0) : Bool :=
  wfR P0 rp.r && P0.dotv rp.r.f P0.x == 0 && verifyBad (withBound (withExtra P0 [rp.r]) Bstab) rp.w

@[expose] def vCover1 (P0 : Pt) (T : NTables) (cand : List Refl) : Bool :=
  (movingOf P0 cand).all fun c => T.orb1.any fun e => reqb e.e c

@[expose] def entry1OK (P0 : Pt) (T : NTables) (e : OEnt) : Bool :=
  wfR P0 e.e && decide (e.j < T.reps.length) &&
    (match T.reps[e.j]? with
     | some rp => realizes (withExtra P0 [e.e]) (e.w ++ [P0.gens.length] ++ e.w.reverse) rp.r
     | none => false)

@[expose] def s2RootsN (P0 : Pt) (rp : NRep) : Bool :=
  rp.roots.all fun ρ => wfR P0 ρ.r && realizes (withExtra P0 [rp.r]) ρ.w ρ.r

@[expose] def s2RepsN (P0 : Pt) (rp : NRep) : Bool :=
  rp.reps2.all fun q => wfR P0 q.r && verifyBad (withExtra P0 [rp.r, q.r]) q.w

@[expose] def s2OrbN (P0 : Pt) (rp : NRep) : Bool :=
  rp.orb2.all fun x => wfR P0 x.e && decide (x.j < rp.reps2.length) &&
    (match rp.reps2[x.j]? with
     | some q => realizes (withExtra P0 [rp.r, x.e]) (x.w ++ [P0.gens.length + 1] ++ x.w.reverse) q.r
     | none => false)

@[expose] def s2CandN (P0 : Pt) (rp : NRep) (c : Refl) : Bool :=
  (rp.roots.map (·.r)).any (reqb c) || asymAny (withExtra P0 [rp.r]) (rp.roots.map (·.r)) c ||
    rp.orb2.any fun x => reqb x.e c

@[expose] def verifyStage2N (P0 : Pt) (cand : List Refl) (rp : NRep) : Bool :=
  s2RootsN P0 rp && s2RepsN P0 rp && s2OrbN P0 rp && (movingOf P0 cand).all (s2CandN P0 rp)

@[expose] def verifyRepN (P0 : Pt) (cand : List Refl) (rp : NRep) : Bool :=
  wfR P0 rp.r && P0.dotv rp.r.f P0.x != 0 &&
  (match rp.kind with
   | .w w =>
     (match w with
      | .weyl _ => verify (withExtra P0 [rp.r]) w && verifyStage2N P0 cand rp
      | .kernel _ => false
      | .transv _ => verify (withExtra P0 [rp.r]) w
      | .order _ => verify (withExtra P0 [rp.r]) w)
   | .cent => centOK P0 rp.r && centRootsOK P0 rp.r rp.roots && verifyStage2N P0 cand rp)

@[expose] def verifyAllN (P0 : Pt) (Bstab : Nat) (T : NTables) : Bool :=
  wfCheck P0 && vFixN P0 && vRootsN P0 T &&
  (let cand := candOfN P0 T
   vCover0 P0 T cand && T.orb0.all (entry0OK P0 T) && T.reps0.all (rep0OK P0 Bstab) &&
   vCover1 P0 T cand && T.orb1.all (entry1OK P0 T) && T.reps.all (verifyRepN P0 cand))


@[expose] def nineBstab : Nat := 4354560

@[expose, reducible] def nineFrame8 (_ : Unit := ()) : Pt :=
  { p := 3, D := 8, nFrame := 8, gens := frame8 (), x := [0, 0, 0, 0, 0, 0, 0, 1], bound := bound9 }

@[expose, reducible] def nineFrame9 (_ : Unit := ()) : Pt :=
  { p := 3, D := 9, nFrame := 8, gens := frame9m (), x := [0, 0, 0, 0, 0, 0, 0, 1, 0], bound := bound9 }


end CFSG.NineAll

end
