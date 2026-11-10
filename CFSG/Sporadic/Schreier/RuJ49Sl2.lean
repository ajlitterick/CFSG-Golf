module

public import CFSG.Sporadic.Schreier.RuJ49Check

public section

namespace CFSG.Sporadic.RuSchreier.J49.Sl2

open CFSG.Monster.B.Co2.Native

set_option compiler.extract_closed false

@[expose] def rowsText : String :=
  include_str "../../../Certificates/Data/CFSGNative/RuSchreier/ruJ49Sl2.txt"


@[expose] def wordOf (R : List (ℕ × List ℤ)) (k : ℕ) : List ℤ := (R.lookup k).getD []

@[expose] def dA (k : ℕ) : ℕ := k % 5

@[expose] def dB (k : ℕ) : ℕ := k / 5 % 5

@[expose] def dC (k : ℕ) : ℕ := k / 25 % 5

@[expose] def dD (k : ℕ) : ℕ := k / 125 % 5

@[expose] def enc (a b c d : ℕ) : ℕ := a + 5 * (b + 5 * (c + 5 * d))

@[expose] def keyMul (k l : ℕ) : ℕ :=
  enc ((dA k * dA l + dB k * dC l) % 5) ((dA k * dB l + dB k * dD l) % 5)
    ((dC k * dA l + dD k * dC l) % 5) ((dC k * dB l + dD k * dD l) % 5)

@[expose] def isSL (k : ℕ) : Bool := (dA k * dD k + 4 * (dB k * dC k)) % 5 == 1

@[expose] def slKeys (_ : Unit := ()) : List ℕ := (List.range 625).filter isSL


end CFSG.Sporadic.RuSchreier.J49.Sl2
