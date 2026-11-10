module

public import CFSG.GF2Type.Smith1979W3.Cert690.Check
public import CFSG.GF2Type.Smith1979W3.Cert690.Dict

public section

namespace CFSG.GF2Type.Smith1979W3.Cert690

open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.O62

@[expose] def oGensC (minus : Bool) : List ℕ :=
  (oWords minus).map wordC

@[expose] def omegaGensC (minus : Bool) : List ℕ :=
  (omegaWords minus).map wordC


structure GrpData where
  O : Array ℕ
  par : Array (ℕ × ℕ)
  invI : Array ℕ
  idx : Std.HashMap ℕ ℕ
  Om : Array ℕ
  OmPar : Array (ℕ × ℕ)

@[expose] def grpData (minus : Bool) (_ : Unit := ()) : GrpData :=
  let d := enumData (oGensC minus)
  let O := d.1
  let idx := idxMapOf O
  let invI := (invArr O).map fun c => idx.getD c O.size
  let e := enumData (omegaGensC minus)
  { O := O, par := d.2, invI := invI, idx := idx, Om := e.1, OmPar := e.2 }

@[expose] def idxOK (D : GrpData) : Bool :=
  (List.range D.O.size).all fun i => D.idx.getD D.O[i]! D.O.size == i

@[expose] def invArrOK (D : GrpData) : Bool :=
  D.invI.size == D.O.size &&
  D.invI.all (fun j => j < D.O.size) &&
  (List.range D.O.size).all fun i =>
    Code.mul D.O[i]! D.O[D.invI[i]!]! == Code.one

@[expose] def groupOK (minus : Bool) (D : GrpData) : Bool :=
  enumOK (oGensC minus) D.O D.par &&
  enumOK (omegaGensC minus) D.Om D.OmPar &&
  D.O.size == (if minus then 51840 else 40320) &&
  D.Om.size == (if minus then 25920 else 20160) &&
  idxOK D && invArrOK D

@[expose] def singOf (minus : Bool) : Array ℕ :=
  ((List.range 64).filter fun n => n != 0 && !(qB minus n)).toArray

@[expose] def b0Of (minus : Bool) : ℕ := (singOf minus)[0]!

@[expose] def transWitOf (D : GrpData) (s : Array ℕ) (b : ℕ) : Array ℕ :=
  s.map fun e => (List.range D.O.size).find? (fun i => Code.act D.O[i]! e == b) |>.getD 0

@[expose] def transOK (D : GrpData) (s : Array ℕ) (b : ℕ) (w : Array ℕ) : Bool :=
  s.size != 0 && w.size == s.size && s[0]! == b &&
  (List.range s.size).all fun k =>
    let i := w[k]!
    i < D.O.size && Code.act D.O[i]! s[k]! == b

@[expose] def isA2Of (D : GrpData) (minus : Bool) (i : ℕ) : Bool :=
  i < D.O.size &&
  let c := D.O[i]!
  c != Code.one && Code.mul c c == Code.one &&
  let I := ((List.range 64).map fun v => Code.act c v ^^^ v).toArray
  (hashSetOfArray I).size == 4 && I.all (fun x => !(qB minus x))

@[expose] def a2FixOf (D : GrpData) (minus : Bool) (b : ℕ) : Array ℕ :=
  ((List.range D.O.size).filter fun i =>
    Code.act D.O[i]! b == b && isA2Of D minus i).toArray

@[expose] def conjIdxOf (D : GrpData) (a x : ℕ) : ℕ :=
  D.idx.getD (Code.mul (Code.mul D.O[a]! D.O[x]!) D.O[D.invI[a]!]!) D.O.size

@[expose] def lOK (D : GrpData) (minus : Bool) (b : ℕ) (L : Array ℕ) : Bool :=
  L.size != 0 && L.contains 0 && (hashSetOfArray L).size == L.size &&
  L.all (fun i =>
    i < D.O.size && Code.act D.O[i]! b == b &&
      (i == 0 || Code.mul D.O[i]! D.O[i]! == Code.one)) &&
  L.all (fun i => L.all fun j =>
    let p := Code.mul D.O[i]! D.O[j]!
    let y := D.idx.getD p D.O.size
    y < D.O.size && D.O[y]! == p && L.contains y) &&
  L.any (isA2Of D minus)

@[expose] def l2OK (D : GrpData) (minus : Bool) (b : ℕ) (Llist : Array (Array ℕ))
    (a2 : Array ℕ) (wit : Array (ℕ × ℕ)) : Bool :=
  wit.size == a2.size &&
  (List.range a2.size).all fun k =>
    let t := a2[k]!
    let j := (wit[k]!).1
    let c := (wit[k]!).2
    j < Llist.size && c < D.O.size && Code.act D.O[c]! b == b &&
    let L := Llist[j]!
    L.size == 2 && L.contains 0 &&
    (let ci := D.O[D.invI[c]!]!
     let cj := fun x =>
       let p := Code.mul (Code.mul D.O[c]! D.O[x]!) ci
       let y := D.idx.getD p D.O.size
       (y < D.O.size && D.O[y]! == p, y)
     L.all (fun x => (cj x).1 && ((cj x).2 == 0 || (cj x).2 == t)) &&
     L.any (fun x => (cj x).1 && (cj x).2 == 0) &&
     L.any (fun x => (cj x).1 && (cj x).2 == t))

@[expose] def l3OK (D : GrpData) (b : ℕ) (Llist : Array (Array ℕ))
    (tasks : Array (ℕ × ℕ)) (wit : Array (ℕ × ℕ)) : Bool :=
  wit.size == tasks.size &&
  (List.range tasks.size).all fun k =>
    let j := (tasks[k]!).1
    let u := (tasks[k]!).2
    let kk := (wit[k]!).1
    let c := (wit[k]!).2
    j < Llist.size && u < D.O.size && kk < Llist.size && c < D.O.size &&
    let L := Llist[j]!
    Code.act D.O[u]! b == b && isInvCode D.O[u]! && !(L.contains u) &&
    L.all (fun x => Code.mul D.O[u]! D.O[x]! == Code.mul D.O[x]! D.O[u]!) &&
    Code.act D.O[c]! b == b &&
    (let U := L ++ L.map (fun x => D.idx.getD (Code.mul D.O[x]! D.O[u]!) D.O.size)
     U.size == 2 * L.size && U.all (fun x => x < D.O.size) &&
     (hashSetOfArray U).size == U.size &&
     (let V := U.map (fun x => conjIdxOf D c x)
      (hashSetOfArray V).size == (Llist[kk]!).size &&
      V.all (fun y => (Llist[kk]!).contains y) &&
      (Llist[kk]!).all (fun y => V.contains y)))

@[expose] def l3TaskValid (D : GrpData) (b : ℕ) (Llist : Array (Array ℕ))
    (j u : ℕ) : Bool :=
  j < Llist.size && u < D.O.size &&
  Code.act D.O[u]! b == b && isInvCode D.O[u]! && !((Llist[j]!).contains u) &&
  (Llist[j]!).all fun x =>
    Code.mul D.O[u]! D.O[x]! == Code.mul D.O[x]! D.O[u]!

@[expose] def l3Complete (D : GrpData) (b : ℕ) (Llist : Array (Array ℕ))
    (tasks : Array (ℕ × ℕ)) : Bool :=
  (List.range Llist.size).all fun j =>
    (List.range D.O.size).all fun u =>
      if l3TaskValid D b Llist j u then tasks.contains (j, u) else true

@[expose] def minCandSize (minus : Bool) : ℕ := if minus then 8 else 4

@[expose] def candidatesOf (minus : Bool) (Llist : Array (Array ℕ)) : Array ℕ :=
  ((List.range Llist.size).filter fun j => (Llist[j]!).size >= minCandSize minus).toArray

structure KSub where
  elems : Array ℕ
  gens : Array ℕ
  par : Array (ℕ × ℕ)
  deriving Inhabited

inductive KClass where
  | normal (N : Array ℕ)
  | reducible (v : ℕ)
  | omega
  | whole
  | pgl (g : ℕ)
  deriving Inhabited

structure CloseWit where
  rep : ℕ
  k : ℕ
  n : ℕ
  words : Array (Array ℕ)
  deriving Inhabited

structure LData where
  Llist : Array (Array ℕ)
  l2wit : Array (ℕ × ℕ)
  l3tasks : Array (ℕ × ℕ)
  l3wit : Array (ℕ × ℕ)
  deriving Inhabited

structure CandData where
  L : Array ℕ
  flist : Array KSub
  bits : Array String
  closes : Array (Array CloseWit)
  classif : Array KClass
  deriving Inhabited

@[expose] def catN (as : Array (Array ℕ)) : Array ℕ :=
  as.foldl (fun acc a => acc ++ a) #[]

@[expose] def catP (as : Array (Array (ℕ × ℕ))) : Array (ℕ × ℕ) :=
  as.foldl (fun acc a => acc ++ a) #[]


@[expose] def censusBaseOf (minus : Bool) (D : GrpData) (Ld : LData) : Bool :=
  groupOK minus D &&
  (let s := singOf minus
   let b := b0Of minus
   let tw := transWitOf D s b
   transOK D s b tw &&
   (let a2 := a2FixOf D minus b
    Ld.Llist.size == (if minus then 17 else 22) &&
    (candidatesOf minus Ld.Llist).size == (if minus then 11 else 20) &&
    Ld.Llist.all (fun L => lOK D minus b L) &&
    l2OK D minus b Ld.Llist a2 Ld.l2wit &&
    l3Complete D b Ld.Llist Ld.l3tasks &&
    l3OK D b Ld.Llist Ld.l3tasks Ld.l3wit))


@[expose] def parseNat (s : String) : ℕ :=
  s.toList.foldl (fun a c => if '0' ≤ c && c ≤ '9' then a * 10 + (c.toNat - 48) else a) 0

@[expose] def parseNats (s : String) : Array ℕ :=
  (s.splitOn " ").filter (fun x => !x.isEmpty) |>.map parseNat |>.toArray

@[expose] def parsePairs (s : String) : Array (ℕ × ℕ) :=
  (s.splitOn ";").filter (fun x => !x.isEmpty) |>.map (fun p =>
    match p.splitOn "," with
    | [a, b] => (parseNat a, parseNat b)
    | _ => (0, 0)) |>.toArray

@[expose] def parseWord (s : String) : Array ℕ :=
  (s.splitOn " ").filter (fun x => !x.isEmpty) |>.map parseNat |>.toArray

@[expose] def parseCloseWit (s : String) : CloseWit :=
  match s.splitOn ":" with
  | [h, ws] =>
    match h.splitOn "," with
    | [a, b, c] =>
      { rep := parseNat a, k := parseNat b, n := parseNat c,
        words := (ws.splitOn "|").map parseWord |>.toArray }
    | _ => default
  | _ => default

@[expose] def parseCloseLine (s : String) : Array CloseWit :=
  if s.isEmpty then #[] else
    (s.splitOn ";").filter (fun x => !x.isEmpty) |>.map parseCloseWit |>.toArray


end CFSG.GF2Type.Smith1979W3.Cert690

end
