module

public import CFSG.LargeExtraspecial.SL4ModNativeBasic

public section

namespace CFSG.LargeExtraspecial.SL4Mod.Native

set_option compiler.extract_closed false


structure CosetData where
  words : Array (List Nat)
  codes : Array (Array Nat)
  invs : Array (Array Nat)
  tau : Array (Array Nat)
  fac : Array (Array (Bool × Nat × Nat))
deriving Inhabited


@[expose] def facCode (j : Nat) (f : Bool) (e₁ e₂ : Nat) : Array Nat :=
  if f then mul4 (mul4 (uCode e₁) (genCode (j + 3))) (uCode e₂) else uCode e₁


@[expose] def checkTau (j : Nat) (d : CosetData) : Bool :=
  (List.range 6).all fun s => (List.range 105).all fun k =>
    let p := d.fac[s]![k]!
    mul4 (genCode s) (wordCode d.words[d.tau[s]![k]! % 105]!) ==
      mul4 (wordCode d.words[k]!) (facCode j p.1 p.2.1 p.2.2)

end CFSG.LargeExtraspecial.SL4Mod.Native
