module

public import CFSG.RankThree.PartOne.KS.PKitLeaf
public import CFSG.RankThree.PartOne.KS.PKitLines

public section

namespace CFSG.HardMathSupport.Dickson.I271.TabSuzB

open Subgroup CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.Monster.B.Mathieu CFSG.Monster.B.Fischer CFSG.RankThree.Native
  CFSG.RankThree.PartOne
open CFSG.Certificates.ChainArrays

@[expose] def pheadOKQ (n : ℕ) (L : Array Level) (base : Array ℕ) (xs : Array (Array ℕ))
    (rels : List (ℕ × ℕ × ℕ)) (T : Array ℕ → Bool) : ℕ → ℕ → Array ℕ → Bool
  | 0, _, acc => T acc
  | fuel + 1, i, acc => allLt (L[i]!).pts.size fun k =>
      !(relOK base xs rels i acc (L[i]!).pts[k]!) ||
        pheadOKQ n L base xs rels T fuel (i + 1) (compA n acc (L[i]!).tr[k]!)

section Facts

variable {n : ℕ} {Q : RawSchreierDatum n} {O S : Array (Array ℕ)} {base : Array ℕ}
  {W : Array (List ℤ)} {chunks : ℕ}
  (hA : ChainArrays Q O S base W) (hF : ChainCheckFacts n O S base W chunks)
  (hQ : ValidSchreier Q)
include hA hF hQ


end Facts

@[expose] def agreeBase (base : Array ℕ) (m : ℕ) (e r : Array ℕ) : Bool :=
  allLt m fun l => e[base[l]!]! == r[base[l]!]!

@[expose] def hasAgree (rs : Array (Array ℕ)) (base : Array ℕ) (m : ℕ) (e : Array ℕ) : Bool :=
  !(allLt rs.size fun j => !(agreeBase base m e rs[j]!))


@[expose] def memBkt (n : ℕ) (B : Array (List (Array ℕ))) (a : Array ℕ) : Bool :=
  (B[bucketIdx n a]!).any (eqA n a)

@[expose] def centFilter (n : ℕ) (base : Array ℕ) (gR : Array (Array ℕ)) (r s : Array ℕ) : Bool :=
  allLt gR.size fun l => allLt base.size fun m =>
    r[s[(gR[l]!)[base[m]!]!]!]! == (gR[l]!)[r[s[base[m]!]!]!]!


@[expose] def tailTest (n : ℕ) (base : Array ℕ) (gR : Array (Array ℕ)) (B : Array (List (Array ℕ)))
    (rs : Array (Array ℕ)) (s : Array ℕ) : Bool :=
  leafNC n gR B s && allLt rs.size fun j =>
    !(centFilter n base gR rs[j]! s) || memBkt n B (compA n rs[j]! s)

@[expose] def centSplitOKP (p n : ℕ) (S : Array (Array ℕ)) (base x : Array ℕ)
    (rels : List (ℕ × ℕ × ℕ)) (rs : Array (Array ℕ)) (m : ℕ) (gR : Array (Array ℕ)) (ps : List ℕ)
    (cR : ArrCert) (N : ℕ) : Bool :=
  let L := rawLevels n S base
  let B := mkBuckets n cR.pts.toList
  relsOKP p n base x rels && enumOK n gR ps cR && cR.pts.size == N &&
    allLt gR.size (fun k => commA n gR[k]! x) &&
    allLt gR.size (fun k => siftA n L base 0 gR[k]!) && siftA n L base 0 x &&
    allLt rs.size (fun j => validA n rs[j]! && commA n rs[j]! x && siftA n L base 0 rs[j]! &&
      leafNC n gR B rs[j]!) &&
    pheadOKQ n L base (powPA p n x) rels (hasAgree rs base m) m 0 (idA n) &&
    ptailOKQ n L base x (powPA p n x) rels (tailTest n base gR B rs) (base.size - m) m (idA n)

section Spec


end Spec

end CFSG.HardMathSupport.Dickson.I271.TabSuzB
