module

public import CFSG.LocalAnalysis.StandardType.GGKacK0

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private local instance (priority := high) k1tabDecidableEqLargeEvenLabel : DecidableEq LargeEvenLabel :=
  fun a b =>
    match a, b with
    | ⟨ta, ra, na⟩, ⟨tb, rb, nb⟩ =>
      if h1 : ta = tb then
        if h2 : ra = rb then
          if h3 : na = nb then isTrue (by cases h1; cases h2; cases h3; rfl)
          else isFalse (by intro h; injection h with _ _ h3'; exact h3 h3')
        else isFalse (by intro h; injection h with _ h2' _; exact h2 h2')
      else isFalse (by intro h; injection h with h1' _ _; exact h1 h1')

private local instance (priority := high) k1tabDecidableEqGGKacOrbit : DecidableEq GGKacOrbit :=
  fun a b =>
    match a, b with
    | ⟨la, qa⟩, ⟨lb, qb⟩ =>
      if h1 : la = lb then
        if h2 : qa = qb then isTrue (by cases h1; cases h2; rfl)
        else isFalse (by intro h; injection h with _ h2'; exact h2 h2')
      else isFalse (by intro h; injection h with h1' _; exact h1 h1')

private local instance (priority := high) k1tabDecidableEqGGKacDatum : DecidableEq GGKacDatum :=
  fun a b =>
    match a, b with
    | ⟨oa, za, sa⟩, ⟨ob, zb, sb⟩ =>
      if h1 : oa = ob then
        if h2 : za = zb then
          if h3 : sa = sb then isTrue (by cases h1; cases h2; cases h3; rfl)
          else isFalse (by intro h; injection h with _ _ h3'; exact h3 h3')
        else isFalse (by intro h; injection h with _ h2' _; exact h2 h2')
      else isFalse (by intro h; injection h with h1' _ _; exact h1 h1')

inductive GGKacTypeCl | A (l : ℕ) | C (l : ℕ) | D (l : ℕ)
  deriving DecidableEq


@[expose] def ggKacTypeClOfLabel : LargeEvenLabel → Option (GGKacTypeCl × Bool × ℕ)
  | ⟨.A, r, n⟩ => some (.A r, false, n)
  | ⟨.twA, r, n⟩ => some (.A r, true, n)
  | ⟨.B, r, n⟩ => if 2 ≤ r then some (.C r, false, n) else none
  | ⟨.C, r, n⟩ => if 2 ≤ r then some (.C r, false, n) else none
  | ⟨.D, r, n⟩ =>
      if 4 ≤ r then some (.D r, false, n) else if r = 3 then some (.A 3, false, n) else none
  | ⟨.twD, r, n⟩ =>
      if 4 ≤ r then some (.D r, true, n) else if r = 3 then some (.A 3, true, n)
      else if r = 2 then some (.A 1, false, 2 * n) else none
  | _ => none


end CFSG.StandardType

end
