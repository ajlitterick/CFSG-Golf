module

public import Certificates.Data.S1277Struct
public import Certificates.Data.S1277Sig

public section

namespace Certificates.Data.S1277Cand

open CFSG.Quasithin.H13.S127.Mod Certificates.Data.S1277Struct Certificates.Data.S1277Sig
  Certificates.Data.S1277Bfs Std

@[expose] def commN (T : KTab) (x y : Nat) : Nat := mulN T (mulN T (mulN T x y) (invN T x)) (invN T y)

@[expose] def phiGensFull (T : KTab) (N : List Nat) : List Nat :=
  N.map (fun x => mulN T x x) ++ N.flatMap fun x => N.map fun y => commN T x y

@[expose] def phiGens (T : KTab) (N : List Nat) : List Nat :=
  sortSet ((phiGensFull T N).foldl (fun (s : HashSet Nat) x => s.insert x) ∅)

@[expose] def phiList (T : KTab) (N : List Nat) : List Nat := sortSet (mulCl T (phiGens T N))

@[expose] def basisOf (T : KTab) (N Pl : List Nat) : List Nat :=
  (N.foldl (fun (st : List Nat × List Nat) x =>
    if st.2.contains x then st else (st.1 ++ [x], st.2 ++ st.2.map (fun s => mulN T x s)))
    ([], Pl)).1

@[expose] def repOf (T : KTab) (basis : List Nat) (e : Nat) : Nat :=
  (List.range basis.length).foldl
    (fun acc i => if e.testBit i then mulN T acc (basis.getD i 0) else acc) (oneN T)

@[expose] def codeTab (T : KTab) (N Pl : List Nat) (d : Nat) : HashMap Nat Nat :=
  let basis := basisOf T N Pl
  (List.range (2 ^ d)).foldl (fun tab e =>
    let r := repOf T basis e
    Pl.foldl (fun t p => t.insert (mulN T r p) e) tab) ∅

@[expose] def plOK (T : KTab) (Pl : List Nat) : Bool :=
  Pl.all (fun x => Pl.all fun y => Pl.contains (mulN T x y)) && Pl.all fun x => Pl.contains (invN T x)

@[expose] def frOK (T : KTab) (N Pl : List Nat) (d : Nat) (tab : HashMap Nat Nat) : Bool :=
  N.length == 2 ^ d * Pl.length &&
  N.all (fun x => tab.getD x 0 < 2 ^ d) &&
  N.all (fun x => N.all fun y => tab.getD (mulN T x y) 0 == (tab.getD x 0 ^^^ tab.getD y 0)) &&
  (List.range (2 ^ d)).all (fun e => N.any fun x => tab.getD x 0 == e) &&
  N.all fun x => (tab.getD x 0 == 0) == Pl.contains x

@[expose] def labelOf (T : KTab) (zN : Nat) (Pl : List Nat) (typ : Nat) (x : Nat) : Nat :=
  if typ = 0 then (if x == zN then 1 else 0)
  else if typ = 1 then (if mulN T x x == oneN T then 0 else 1)
  else (if Pl.all (fun p => mulN T x p == mulN T p x) then 1 else 0)

@[expose] def phiTab (T : KTab) (zN : Nat) (Pl N : List Nat) (typ d : Nat)
    (tab : HashMap Nat Nat) : List Nat :=
  (List.range (2 ^ d)).map fun e =>
    match N.find? (fun x => tab.getD x 0 == e) with
    | some x => labelOf T zN Pl typ x
    | none => 0

@[expose] def phiFn (pt : List Nat) (e : Nat) : Nat := pt.getD e 0

@[expose] def phiOK (T : KTab) (zN : Nat) (Pl N : List Nat) (typ d : Nat)
    (tab : HashMap Nat Nat) : Bool :=
  let pt := phiTab T zN Pl N typ d tab
  N.all fun x => phiFn pt (tab.getD x 0) == labelOf T zN Pl typ x


@[expose] def isInvB (B : B6) : Bool := B.comp B == B6.id && B != B6.id

@[expose] def fixCode (B : B6) : List Nat := (List.range 64).filter fun c => B.app c == c

@[expose] def fixInterL (B₁ B₂ : B6) : List Nat :=
  (List.range 64).filter fun c => B₁.app c == c && B₂.app c == c


end Certificates.Data.S1277Cand

end
