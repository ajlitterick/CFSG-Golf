module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co2ThreeKit

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzT

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.Proving CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native CFSG.RankThree.Native
  CFSG.Certificates.ChainArrays

variable {n : ℕ}

@[expose] def fltOK : Option (Array ℕ) → ℕ → Bool
  | none, _ => true
  | some f, q => f[q]! == q

@[expose] def fsearch (n : ℕ) (L : Array Level) (base : Array ℕ)
    (rels : Array (Option (ℕ × Array ℕ))) (flt : Array (Option (Array ℕ)))
    (pred : Array ℕ → Bool) : ℕ → ℕ → Array ℕ → Array ℕ → List (Array ℕ)
  | 0, _, acc, _ => if pred acc then [acc] else []
  | fuel + 1, i, acc, accI =>
    match rels.getD i none with
    | some (j, y) =>
      if (L[i]!).pos[accI[y[acc[base[j]!]!]!]!]! < (L[i]!).pts.size then
        fsearch n L base rels flt pred fuel (i + 1)
          (compA n acc (L[i]!).tr[(L[i]!).pos[accI[y[acc[base[j]!]!]!]!]!]!)
          (compA n (L[i]!).trInv[(L[i]!).pos[accI[y[acc[base[j]!]!]!]!]!]! accI)
      else []
    | none =>
      (List.range (L[i]!).pts.size).flatMap fun k =>
        if fltOK (flt.getD i none) acc[((L[i]!).tr[k]!)[base[i]!]!]! then
          fsearch n L base rels flt pred fuel (i + 1) (compA n acc (L[i]!).tr[k]!)
            (compA n (L[i]!).trInv[k]! accI)
        else []


section Facts


end Facts

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzT
