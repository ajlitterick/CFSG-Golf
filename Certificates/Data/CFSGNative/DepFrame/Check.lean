module

public import Certificates.Data.CFSGNative.NineAll.Check

public section

namespace CFSG.DepFrame

open CFSG.TwoNodeSmall CFSG.ReflExt CFSG.NineAll

set_option compiler.extract_closed false

@[expose] def e6Edge (i j : Nat) : Bool :=
  (i == 0 && j == 2) || (i == 2 && j == 0) || (i == 1 && j == 3) || (i == 3 && j == 1) ||
  (i == 2 && j == 3) || (i == 3 && j == 2) || (i == 3 && j == 4) || (i == 4 && j == 3) ||
  (i == 4 && j == 5) || (i == 5 && j == 4)

@[expose] def verifyWE6 (P : Pt) (c : WWit) : Bool :=
  c.sigma.length == 6 &&
  c.sigma.all (fun s => P.wordOK s.1 && decide (s.2 < P.gens.length)) &&
  (let S := c.sigma.map fun s => P.sigmaVecs s.1 s.2
   S.all (fun cb => P.dotv cb.2 cb.1 == 2 % P.p) &&
   (List.range 6).all (fun i => (List.range 6).all fun j =>
     i == j ||
       (let a := P.dotv (S.getD i ([], [])).2 (S.getD j ([], [])).1
        let b := P.dotv (S.getD j ([], [])).2 (S.getD i ([], [])).1
        if e6Edge i j then (a * b) % P.p == 1 else a == 0 && b == 0)) &&
   c.expr.length == P.gens.length &&
   ((c.expr.zip P.gens).all fun (w, r) =>
      w.all (fun i => decide (i < 6)) &&
        (List.range P.D).all fun j =>
          P.vecEq (P.sigmaWord S w (P.unit j)) (P.applyRefl r (P.unit j)))) &&
  verifyO P c.chain 51839


@[expose] def verifyRepD (P0 : Pt) (cand : List Refl) (rp : NRep) : Bool :=
  wfR P0 rp.r && P0.dotv rp.r.f P0.x != 0 &&
  (match rp.kind with
   | .w w =>
     (match w with
      | .weyl c =>
        wfCheck (withExtra P0 [rp.r]) && verifyWE6 (withExtra P0 [rp.r]) c && verifyStage2N P0 cand rp
      | .kernel _ => false
      | .transv _ => verify (withExtra P0 [rp.r]) w
      | .order _ => verify (withExtra P0 [rp.r]) w)
   | .cent => centOK P0 rp.r)

@[expose] def centEntryOK (P0 : Pt) (T : NTables) (e : OEnt) : Bool :=
  match T.reps[e.j]? with
  | some rp =>
    (match rp.kind with
     | .cent => reqb e.e rp.r || reqb e.e (negR P0 rp.r)
     | .w _ => true)
  | none => false

@[expose] def verifyAllD (P0 : Pt) (Bstab : Nat) (T : NTables) : Bool :=
  wfCheck P0 && vFixN P0 && vRootsN P0 T &&
  (let cand := candOfN P0 T
   vCover0 P0 T cand && T.orb0.all (entry0OK P0 T) && T.reps0.all (rep0OK P0 Bstab) &&
   vCover1 P0 T cand && T.orb1.all (entry1OK P0 T) && T.reps.all (verifyRepD P0 cand) &&
   T.orb1.all (centEntryOK P0 T))


end CFSG.DepFrame

end
