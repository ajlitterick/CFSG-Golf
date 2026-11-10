module

@[expose] public section

namespace Certificates.Data.E6TableT

abbrev Vec := List Int

def cartan : List Vec :=
  [[2, 0, -1, 0, 0, 0],
   [0, 2, 0, -1, 0, 0],
   [-1, 0, 2, -1, 0, 0],
   [0, -1, -1, 2, -1, 0],
   [0, 0, 0, -1, 2, -1],
   [0, 0, 0, 0, -1, 2]]

def dot (x y : Vec) : Int := (List.zipWith (· * ·) x y).sum

def iform (x y : Vec) : Int := dot x (cartan.map (dot y))

def basisVec (i : Nat) : Vec := (List.range 6).map fun j => if i = j then 1 else 0

def scalarMul (a : Int) (v : Vec) : Vec := v.map fun x => a * x

def reflect (i : Nat) (v : Vec) : Vec := v - scalarMul (dot (cartan.getD i []) v) (basisVec i)

def closureStep (acc frontier : List Vec) : List Vec :=
  (frontier.foldl (fun (p : List Vec × List Vec) v =>
    (List.range 6).foldl (fun (p : List Vec × List Vec) i =>
      let w := reflect i v
      if acc.contains w || p.2.contains w then p else (p.1, p.2 ++ [w])) p) (acc, [])).2

def closure (fuel : Nat) (acc frontier : List Vec) : List Vec :=
  match fuel with
  | 0 => acc
  | fuel + 1 =>
      let new := closureStep acc frontier
      if new.isEmpty then acc else closure fuel (acc ++ new) new

def roots (_ : Unit := ()) : List Vec :=
  closure 30 ((List.range 6).map basisVec) ((List.range 6).map basisVec)

def genAct (j : Nat) (v : Vec) : Vec :=
  if j < 6 then
    (List.range 6).map fun k => (v.getD k 0 - (cartan.getD j []).getD k 0 * v.getD j 0) % 3
  else
    v.map fun x => (-x) % 3

def orbitStep (acc frontier : List Vec) : List Vec :=
  (frontier.foldl (fun (p : List Vec × List Vec) v =>
    (List.range 7).foldl (fun (p : List Vec × List Vec) j =>
      let w := genAct j v
      if p.1.contains w || p.2.contains w then p else (p.1, p.2 ++ [w])) p) (acc, [])).2

def orbitAux (fuel : Nat) (acc frontier : List Vec) : List Vec :=
  match fuel with
  | 0 => acc
  | fuel + 1 =>
      let new := orbitStep acc frontier
      if new.isEmpty then acc else orbitAux fuel (acc ++ new) new

def orbit (v : Vec) : List Vec := orbitAux 800 [v] [v]

def repD5 : Vec := [0, 0, 0, 0, 0, 1]

def repA4A1 : Vec := [0, 0, 0, 0, 1, 0]

def repA5 : Vec := [0, 0, 0, 0, 1, 1]

def repA2 : Vec := [0, 0, 0, 1, 0, 0]

def repD4 : Vec := [0, 0, 1, 1, 1, 0]

def reps : List Vec := [repA2, repA4A1, repD4, repA5, repD5]

def allVecs (_ : Unit := ()) : List Vec :=
  (List.range 3).flatMap fun a =>
  (List.range 3).flatMap fun b =>
  (List.range 3).flatMap fun c =>
  (List.range 3).flatMap fun d =>
  (List.range 3).flatMap fun e =>
  (List.range 3).flatMap fun f =>
    let v : Vec := [Int.ofNat a, Int.ofNat b, Int.ofNat c, Int.ofNat d, Int.ofNat e, Int.ofNat f]
    if v.any (fun x => x != 0) then [v] else []

def coverOK (_ : Unit := ()) : Bool :=
  let os := reps.map orbit
  (allVecs ()).all fun v => os.any fun o => o.contains v

def kerRootsOf (R : List Vec) (v : Vec) : List Vec :=
  R.filter fun g => dot g v % 3 == 0

def kerRoots (v : Vec) : List Vec := kerRootsOf (roots ()) v

def classStep (ker acc frontier : List Vec) : List Vec :=
  (frontier.foldl (fun (p : List Vec × List Vec) a =>
    ker.foldl (fun (p : List Vec × List Vec) b =>
      if p.1.contains b || p.2.contains b then p
      else if iform a b != 0 then (p.1, p.2 ++ [b]) else p) p) (acc, [])).2

def classAux (fuel : Nat) (ker acc frontier : List Vec) : List Vec :=
  match fuel with
  | 0 => acc
  | fuel + 1 =>
      let new := classStep ker acc frontier
      if new.isEmpty then acc else classAux fuel ker (acc ++ new) new

def classesOf (ker : List Vec) : List (List Vec) :=
  (ker.foldl (fun (p : List (List Vec) × List Vec) x =>
    if p.2.contains x then p
    else
      let comp := classAux ker.length ker [x] [x]
      (p.1 ++ [comp], p.2 ++ comp)) ([], [])).1

def classes (v : Vec) : List (List Vec) := classesOf (kerRoots v)

def act (b : List Vec) (g : Vec) : Vec :=
  (List.range 6).foldl (fun acc i => acc + scalarMul (g.getD i 0) (b.getD i []))
    (List.replicate 6 0)


def followOrbit (pi : List Nat) : Nat → Nat → List Nat → List Nat
  | 0, _, seen => seen
  | fuel + 1, cur, seen =>
      if seen.contains cur then seen else followOrbit pi fuel (pi.getD cur cur) (seen ++ [cur])


def closedOK (_ : Unit := ()) : Bool :=
  let R := roots ()
  R.length == 72 &&
  (List.range 6).all (fun i => R.contains (basisVec i)) &&
  R.all (fun v => (List.range 6).all (fun i => R.contains (reflect i v)))


end Certificates.Data.E6TableT

end
