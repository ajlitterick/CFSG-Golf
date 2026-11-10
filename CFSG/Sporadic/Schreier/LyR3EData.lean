module
public import Certificates.Certificate3085


public noncomputable section

namespace CFSG.Sporadic.LySchreier

open CFSG.Sporadic.Ly

@[expose] def r3eH : J := (a * b) * lyz * (a * b)⁻¹

@[expose] def r3eG : J := (r3eH * lyf) ^ 7 * (lyz * r3eH) ^ 4

@[expose] def r3eWords : List (List ℤ) :=
  [[12], [6, 6, -12, 8, 10, 9], [5, 5, 5, 9, 6, 10, -11], [6, -11],
    [-6, 5, -6, -6, 7, 6, 8, 10, 9, 12, 11, 12], [2, 12, 1, -8, 6, -11, -12]]

@[expose] def r3eD (k : ℕ) : J := evalWord cStar (r3eWords.getD k [])

@[expose] def r3eD0 :
    Subgroup J := Subgroup.closure ({lyz, lyf} ∪ r3eD '' Set.Iio 6)

@[expose] def r3eC : J := cStar 3


@[expose] def r3eFusionWord : List ℤ := [3, 2, 3, 2]

@[expose] def r3eFusion : J :=
  evalWord (fun k => if h : k < 6 then sylowGen ⟨k, h⟩ else 1) r3eFusionWord


end CFSG.Sporadic.LySchreier
