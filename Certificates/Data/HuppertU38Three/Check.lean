module

public import Certificates.Data.HuppertU38Three.Data
public import Certificates.Data.HuppertU38Q.NoE81
public import CFSG.RankThree.PartOne.KS.PKit
public import CFSG.RankThree.PartOne.KS.PKitLines
public import Mathlib

public section

namespace U38Three

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native
  CFSG.RankThree.PartTwo.Sec4.Item434U38 CFSG.RankThree.PartOne U38Sylow

@[expose] def fix01 (a : Array ℕ) : Bool := a[0]! == 0 && a[1]! == 1

@[expose] def rels3 : List (ℕ × ℕ × ℕ) := [(0, 0, 1), (1, 1, 1), (2, 2, 1)]

@[expose] def keyPts9 : List ℕ := [0, 1, 2]

@[expose] def hCert (_ : Unit := ()) : ArrCert := enumBfs 513 hGens keyPts 400

@[expose] def lCert (_ : Unit := ()) : ArrCert := enumBfs 513 #[la, lb] keyPts 600

@[expose] def cCert (_ : Unit := ()) : ArrCert := enumBfs 513 cGens keyPts 1600

@[expose] def pCert (_ : Unit := ()) : ArrCert := enumBfs 9 #[pa, pb] keyPts9 600

@[expose] def cubeIdx (pts : Array (Array ℕ)) : List ℕ :=
  (List.range pts.size).filter fun j => cubeOne pts[j]!

@[expose] def hElemCheck (pts : Array (Array ℕ)) (d e : Array ℕ) : Bool :=
  let cs := cubeIdx pts
  cs.all fun i => eqA 513 pts[i]! (idA 513) || eqA 513 pts[i]! d || eqA 513 pts[i]! e ||
    (commAt pts[i]! d && decide ((cs.filter fun j => commAt pts[i]! pts[j]!).length ≤ 9))

@[expose] def conjGensM (n m : ℕ) (c : ArrCert) (k : ℕ) : Array (Array ℕ) :=
  Array.ofFn (n := m) fun j => conjA n c.pts[j.val]! c.pts[k]!


@[expose] def memPts (c : ArrCert) (x : Array ℕ) : Bool := c.pts.toList.any (eqA 513 x)


end U38Three
