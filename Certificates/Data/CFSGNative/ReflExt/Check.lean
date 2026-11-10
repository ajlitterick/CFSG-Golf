module

public import Certificates.Data.CFSGNative.ReflExt.Core
public import Certificates.Data.CFSGNative.TwoNodeSmall.SearchPos

public section

namespace CFSG.ReflExt

open CFSG.TwoNodeSmall

set_option compiler.extract_closed false


@[expose] def Rep.isGoodMax (rp : Rep) : Bool :=
  match rp.kind with
  | .good _ => rp.maximal
  | .bad _ => false

@[expose] def s2Roots (P0 : Pt) (rp : Rep) : Bool :=
  rp.roots.all fun ρ => wfR P0 ρ.r && realizes (withExtra P0 [rp.r]) ρ.w ρ.r

@[expose] def s2Reps (P0 : Pt) (rp : Rep) : Bool :=
  rp.reps2.all fun q => wfR P0 q.r && wfCheck (withExtra P0 [rp.r, q.r]) &&
    verifyO (withExtra P0 [rp.r, q.r]) q.o P0.bound

@[expose] def s2Orb (P0 : Pt) (rp : Rep) : Bool :=
  rp.orb2.all fun x => wfR P0 x.e && decide (x.j < rp.reps2.length) &&
    (match rp.reps2[x.j]? with
     | some q => realizes (withExtra P0 [rp.r, x.e]) (x.w ++ [P0.gens.length + 1] ++ x.w.reverse) q.r
     | none => false)

@[expose] def s2Cand (P0 : Pt) (T : Tables) (rp : Rep) (c : Refl) : Bool :=
  (rp.roots.map (·.r)).any (reqb c) || asymAny (withExtra P0 [rp.r]) (rp.roots.map (·.r)) c ||
    rp.orb2.any (fun x => reqb x.e c) ||
    (!rp.maximal && T.orb1.any fun e => reqb e.e c &&
      (match T.reps[e.j]? with | some rq => rq.isGoodMax | none => false))

@[expose] def verifyStage2 (P0 : Pt) (T : Tables) (cand : List Refl) (rp : Rep) : Bool :=
  s2Roots P0 rp && s2Reps P0 rp && s2Orb P0 rp && cand.all (s2Cand P0 T rp)

@[expose] def verifyRep (P0 : Pt) (T : Tables) (cand : List Refl) (rp : Rep) : Bool :=
  wfR P0 rp.r && wfCheck (withExtra P0 [rp.r]) &&
  (match rp.kind with
   | .bad o => verifyO (withExtra P0 [rp.r]) o P0.bound
   | .good c => verifyWPos (withExtra P0 [rp.r]) c && verifyStage2 P0 T cand rp)

@[expose] def candOf (P0 : Pt) (T : Tables) : List Refl := candList P0 (T.roots.map (·.r))

@[expose] def vRoots (P0 : Pt) (T : Tables) : Bool :=
  T.roots.all fun ρ => wfR P0 ρ.r && realizes P0 ρ.w ρ.r && P0.dotv ρ.r.f P0.x == 0

@[expose] def vCover (P0 : Pt) (T : Tables) (cand : List Refl) : Bool :=
  (movingOf P0 cand).all fun c => T.orb1.any fun e => reqb e.e c

@[expose] def entryOK (P0 : Pt) (T : Tables) (e : OEnt) : Bool :=
  wfR P0 e.e && decide (e.j < T.reps.length) &&
    (match T.reps[e.j]? with
     | some rp => realizes (withExtra P0 [e.e]) (e.w ++ [P0.gens.length] ++ e.w.reverse) rp.r
     | none => false)

@[expose] def verifyAll (P0 : Pt) (T : Tables) : Bool :=
  wfCheck P0 && vRoots P0 T &&
  (let cand := candOf P0 T
   vCover P0 T cand && T.orb1.all (entryOK P0 T) && T.reps.all (verifyRep P0 T cand))


@[expose, reducible] def unitV (D k : Nat) : Vec := (List.range D).map fun j => if j = k then 1 else 0

@[expose, reducible] def mkFrame (p n D : Nat) (row : Nat → Vec) (s : Nat) (xl : Vec) (bound : Nat) : Pt :=
  { p := p, D := D, nFrame := n,
    gens := (List.range n).map fun i =>
      ⟨row i ++ (if D = n + 1 then [if i = 0 then s else 0] else []), unitV D i⟩,
    x := xl ++ (if D = n + 1 then [0] else []),
    bound := bound }


end CFSG.ReflExt

end
