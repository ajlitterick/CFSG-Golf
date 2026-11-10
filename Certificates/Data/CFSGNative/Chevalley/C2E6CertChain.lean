module

public import Certificates.Data.CFSGNative.Chevalley.C2E6CertOrbit

public section

namespace CFSG.Monster.Existence.StdOdd.CertNative

open CFSG.LieType.Chevalley.C2E6Std.MatrixModel.Native

structure ChainData where
  p : Nat
  xw : List (Nat × Bool)
  d0 : List (Nat × Bool)
  e : List Nat
  ks : List Nat
  prog : List (List Nat)
  regs : List (List (Nat × Nat))
  Lvals : List Nat
  N : Nat
  sizeS : Nat

instance : Inhabited ChainData := ⟨⟨0, [], [], [], [], [], [], [], 0, 0⟩⟩

structure Forest where
  pts : Array Vec
  par : Array Nat
  lab : Array Nat
  idx : Vec → Nat

instance : Inhabited Forest := ⟨⟨#[], #[], #[], fun _ => 0⟩⟩


@[expose] def forestAt (T : Array (Array Vec)) (f : Forest) (root : Vec) (k : Nat) : Bool :=
  let u := f.pts.getD k (0, 0)
  isCanon u && f.idx u == k &&
    (if k == 0 then u == root else
      f.par.getD k 0 < k && f.lab.getD k 0 < T.size &&
        u == applyT (T.getD (f.lab.getD k 0) #[]) (f.pts.getD (f.par.getD k 0) (0, 0)))

@[expose] def forestOK (T : Array (Array Vec)) (f : Forest) (root : Vec) (chunks : Nat) : Bool :=
  0 < f.pts.size && parAll f.pts.size chunks (forestAt T f root)

@[expose] def walkUp (par lab : Array Nat) (inv : Array (Array Vec)) (k : Nat) (u : Vec) : Vec :=
  if _h : 0 < k ∧ par.getD k 0 < k then
    walkUp par lab inv (par.getD k 0) (applyT (inv.getD (lab.getD k 0) #[]) u)
  else u
termination_by k
decreasing_by exact _h.2

structure LevelData where
  forest : Forest
  fwd : Array (Array Vec)
  inv : Array (Array Vec)
  dT : Array Vec
  root : Vec

instance : Inhabited LevelData := ⟨⟨default, #[], #[], #[], (0, 0)⟩⟩


structure Prep where
  vals : Array Mat
  Mx : Mat
  TMx : Array Vec
  b : Vec
  xOrb : Array Vec


@[expose] def betaN (prep : Prep) (d : ChainData) (i : Nat) : Vec :=
  prep.xOrb.getD (d.e.getD i 0) (0, 0)

@[expose] def rootOf (prep : Prep) (d : ChainData) (i : Nat) : Vec :=
  if i == 0 then e7 else betaN prep d i

@[expose] def dMatOf (A B : Mat) (d : ChainData) (i : Nat) : Mat :=
  if i == 0 then wordMat A B d.d0 else one

@[expose] def fwdTbls (vals : Array Mat) (regs : List (Nat × Nat)) : Array (Array Vec) :=
  (regs.map fun r => mkTbl (vals.getD r.1 one)).toArray

@[expose] def invTbls (vals : Array Mat) (regs : List (Nat × Nat)) : Array (Array Vec) :=
  (regs.map fun r => mkTbl (vals.getD r.2 one)).toArray


@[expose] def levelAt (A B : Mat) (prep : Prep) (d : ChainData) (lv : Array Forest) (i : Nat) :
    LevelData :=
  ⟨lv.getD i default, fwdTbls prep.vals (d.regs.getD i []), invTbls prep.vals (d.regs.getD i []),
    mkTbl (dMatOf A B d i), rootOf prep d i⟩

@[expose] def mkLevelData (A B : Mat) (prep : Prep) (d : ChainData) (lv : Array Forest) :
    List LevelData :=
  (List.range d.p).map (levelAt A B prep d lv)

@[expose] def regOK (vals : Array Mat) (beta : Nat → Vec) (i : Nat) (r : Nat × Nat) : Bool :=
  let M := vals.getD r.1 one
  let M' := vals.getD r.2 one
  let T := mkTbl M
  matCanonB M' && eqM (mul M M') one && (List.range i).all fun j => applyT T (beta j) == beta j

@[expose] def levelOK (chunks : Nat) (prep : Prep) (d : ChainData) (L : LevelData) (i : Nat) :
    Bool :=
  (d.regs.getD i []).all (regOK prep.vals (betaN prep d) i) &&
    forestOK L.fwd L.forest L.root chunks && applyT L.dT L.root == betaN prep d i

@[expose] def distinctM : List Mat → Bool
  | [] => true
  | M :: Ms => Ms.all (fun M' => !eqM M M') && distinctM Ms

@[expose] def orderR (_ : Unit := ()) : Nat := 76532479683774853939200

@[expose] def prodOK (ld : List LevelData) (d : ChainData) : Bool :=
  (List.range d.p).foldl (fun a i => a * (ld.getD i default).forest.pts.size) 1 * d.Lvals.length ==
    orderR

@[expose] def LOK (prep : Prep) (d : ChainData) : Bool :=
  let Ms := d.Lvals.map fun v => prep.vals.getD v one
  Ms.all (fun M => let T := mkTbl M
    (List.range d.p).all fun j => applyT T (betaN prep d j) == betaN prep d j) &&
    Ms.all (fun M => eqM (mul M prep.Mx) (mul prep.Mx M)) && distinctM Ms &&
    Nat.gcd d.Lvals.length d.p == 1

@[expose] def basicOK (d : ChainData) : Bool :=
  0 < d.p && d.e.length == d.p && d.regs.length == d.p && d.e.getD 0 1 == 0 &&
    (List.range d.p).all (fun j => d.e.contains j) &&
    d.e.all (fun j => j < d.p) && d.ks.all (fun k => 0 < k && k < d.p) &&
    d.regs.getD 0 [] == [(0, 0), (1, 2)]


@[expose] def tinv (L : LevelData) (k : Nat) (u : Vec) : Vec :=
  applyT L.dT (walkUp L.forest.par L.forest.lab L.inv k u)


@[expose] def chainCheck (A B : Mat) (chunks : Nat) (prep : Prep) (lv : Array Forest)
    (d : ChainData) : Bool :=
  basicOK d &&
    (let ld := mkLevelData A B prep d lv
     (List.range d.p).all (fun i => levelOK chunks prep d (ld.getD i default) i) &&
       prodOK ld d && LOK prep d)


end CFSG.Monster.Existence.StdOdd.CertNative
