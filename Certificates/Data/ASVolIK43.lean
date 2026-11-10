module

public import CFSG.Quasithin.Background.HMathieuSyl24Inputs
public import CFSG.Quasithin.Background.HMathieuCodeMask
public import Std.Data.HashSet
public meta import CFSG.Quasithin.Background.HMathieuSyl24Inputs
public meta import CFSG.Quasithin.Background.HMathieuCentInputs
public meta import CFSG.Quasithin.Background.HMathieuCodeMask
public meta import CFSG.Quasithin.Background.HMathieuMask
public meta import CFSG.Quasithin.Background.HMathieuBits
public meta import CFSG.Monster.Code.Basis

public section

namespace CFSG.ASVolI.K43Data

open CFSG.Quasithin.H.Mathieu CFSG.Monster.Code CFSG.QuasithinUnique.Setup.X1


@[expose] def moGens : List (Array ℕ) :=
  [#[1, 21, 16, 19, 4, 22, 2, 7, 13, 6, 10, 17, 0, 14, 23, 15, 9, 20, 11, 3, 18, 12, 5, 8],
    #[3, 4, 7, 0, 1, 6, 5, 2, 8, 15, 12, 11, 10, 13, 14, 9, 22, 17, 18, 21, 20, 19, 16, 23],
    #[6, 2, 1, 5, 7, 3, 0, 4, 8, 12, 15, 11, 9, 13, 14, 10, 21, 17, 18, 22, 20, 16, 19, 23],
    #[7, 5, 10, 0, 1, 9, 19, 16, 17, 4, 12, 23, 22, 14, 18, 6, 3, 11, 20, 21, 13, 15, 2, 8],
    #[7, 10, 9, 4, 15, 2, 1, 12, 8, 5, 6, 11, 0, 13, 14, 3, 19, 17, 20, 21, 23, 16, 22, 18],
    #[10, 19, 22, 12, 21, 9, 15, 16, 8, 5, 0, 11, 3, 13, 14, 6, 7, 17, 18, 1, 20, 4, 2, 23],
    #[12, 0, 6, 22, 7, 19, 9, 4, 11, 16, 15, 14, 21, 17, 20, 10, 2, 23, 13, 5, 8, 1, 3, 18],
    #[21, 5, 0, 16, 3, 19, 22, 6, 8, 9, 15, 11, 10, 13, 14, 12, 4, 20, 17, 1, 18, 2, 7, 23],
    #[21, 12, 9, 19, 10, 22, 16, 15, 8, 2, 4, 11, 1, 13, 14, 7, 6, 17, 18, 3, 20, 0, 5, 23],
    #[22, 7, 4, 21, 1, 16, 19, 2, 14, 10, 12, 11, 15, 13, 8, 9, 3, 18, 17, 0, 20, 5, 6, 23]]


@[expose] def w5Basis : List ℕ := [3, 216, 297, 592, 1096]


@[expose] def w5Masks (_ : Unit := ()) : List ℕ := combos w5Basis


@[expose] def wordsOfLen : ℕ → ℕ → List (List ℕ)
  | 0, _ => [[]]
  | k + 1, n => (wordsOfLen k n).flatMap fun w => (List.range n).map (· :: w)

@[expose] def wordPool (n L : ℕ) : List (List ℕ) := (List.range (L + 1)).flatMap fun k => wordsOfLen k n

@[expose] def pick6 (cands : List ℕ) : List ℕ :=
  cands.foldl (fun acc x => if acc.length < 6 && !(combos acc).contains x then x :: acc else acc) []


end CFSG.ASVolI.K43Data
