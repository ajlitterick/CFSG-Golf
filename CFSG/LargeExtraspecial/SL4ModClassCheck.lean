module

public import CFSG.LargeExtraspecial.SL4ModNativeSpin

public section

namespace CFSG.LargeExtraspecial.SL4Mod.Native

open CFSG.Sporadic.SmallF2.Native


structure ClassCert where
  L : Array Nat
  src : Array (Nat × Nat)
  kind : Nat
  masks : Array Nat
  piv : Array Nat
  sel : Nat
  B : Array Nat
  coef : Array Nat
  mB : Nat
  ref : Nat
deriving Inhabited

@[expose] def echelonOK (n : Nat) (L masks piv : Array Nat) : Bool :=
  decide (n ≤ masks.size) && decide (n ≤ piv.size) &&
    (List.range n).all fun k =>
      decide (piv[k]! < 105) && (xorSel masks[k]! L).testBit piv[k]! &&
        (List.range n).all fun j => decide (j ≤ k) || !((xorSel masks[j]! L).testBit piv[k]!)

@[expose] def closedC (taus : Array (Array Nat)) (B coef : Array Nat) : Bool :=
  (List.range B.size).all fun t => (List.range 6).all fun s =>
    xorSel coef[6 * t + s]! B == actV taus[s]! B[t]!

@[expose] def refOK (taus : Array (Array Nat)) (L : Array Nat) (rows : Array (Array Nat)) : Bool :=
  decide (rows.size = 6) && (List.range 6).all fun s =>
    decide (rows[s]!.size = L.size) && (List.range L.size).all fun k =>
      xorSel rows[s]![k]! L == actV taus[s]! L[k]!

@[expose] def validClass (d : Nat) (refs : Array (Array (Array Nat))) (taus : Array (Array Nat))
    (m : Nat) (c : ClassCert) : Bool :=
  derivOK taus m c.L c.src &&
    (if c.kind == 0 then decide (d + 1 ≤ c.L.size) && echelonOK (d + 1) c.L c.masks c.piv
    else if c.kind == 1 then
      nz (xorSel c.sel c.L) && decide (c.B.size < d) &&
        (xorSel c.mB c.B == xorSel c.sel c.L) && closedC taus c.B c.coef
    else if c.kind == 2 then
      decide (c.L.size = d) && decide (c.ref < refs.size) && refOK taus c.L refs[c.ref]!
    else false)


end CFSG.LargeExtraspecial.SL4Mod.Native
