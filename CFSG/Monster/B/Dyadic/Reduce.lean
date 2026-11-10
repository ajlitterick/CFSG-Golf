module

public import CFSG.Monster.B.Dyadic.Contain
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.Monster.B.Dyadic

open CFSG.Monster.B.Dyadic.Native


@[expose] def numerAt (j t u : ℕ) : ℤ :=
  ((CFSG.Monster.B.Native.packetRows[j]!)[t]!).foldl (fun s e => if e.1 = u then s + e.2 else s) 0


theorem numer_eq_numerAt (g t u : ℕ) : numer g t u = numerAt (selIdx g) t u := rfl


end CFSG.Monster.B.Dyadic
