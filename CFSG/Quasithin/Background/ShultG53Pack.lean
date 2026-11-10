module

public import CFSG.Quasithin.Background.ShultG53Model
public import CFSG.Permutation.FinPackEven6
public import CFSG.Permutation.FinPackF2

public section

namespace CFSG.Quasithin.ShultG53.Pack

open CFSG.Permutation.FinPack CFSG.CharacterTheory.SteinbergBY.AlternatingSix Equiv Matrix

@[expose] def heartT : ℕ := 5278959

@[expose] def hd (c i : ℕ) : ℕ := rd heartT (rd c i)

@[expose] def hK (c x : ℕ) : ℕ :=
  linK (Nat.xor (hd c 0) (hd c 1)) (Nat.xor (hd c 1) (hd c 2)) (Nat.xor (hd c 2) (hd c 3))
    (Nat.xor (hd c 3) (hd c 4)) x


@[expose] def l5 : List ℕ := [0, 1, 2, 3, 4]

@[expose] def l6 : List ℕ := [0, 1, 2, 3, 4, 5]


end CFSG.Quasithin.ShultG53.Pack
