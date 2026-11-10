module

public import CFSG.Sporadic.Schreier.TitsCentralCheckInputs
public import Std.Data.HashMap

public section

namespace Certificates.Thm49E

open CFSG.Sporadic.Schreier.Tits CFSG.Monster.B.Co2.Native

abbrev E : Type := Bool × Array ℕ


structure Orb (α : Type) where
  ls : Array α
  par : Array ℕ
  gen : Array ℕ


@[expose] def zpWord : List ℤ := [-2, -2]

@[expose] def y0Word : List ℤ := [-2, -2, -2, -4, 3, 2, 4, 1, 4, 3, 4, -3, -4, -3]

@[expose] def u1Word : List ℤ := [-4, 2, 1, 4, 1, -2, 4, 1, -2]

@[expose] def u2Word : List ℤ := [-2, -4, -2, 3, 4, 3, 2, 3, 4, 3]

@[expose] def l2Word : List ℤ := [-2, -4, 2, 1, -2, 3, 2, 2, 3, 4, -1, -2]

@[expose] def l3Word : List ℤ := [-4]

@[expose] def h1Word : List ℤ := [3, 4, 3, 2, 3, 4, 3]

@[expose] def h2Word : List ℤ := [2]


end Certificates.Thm49E
