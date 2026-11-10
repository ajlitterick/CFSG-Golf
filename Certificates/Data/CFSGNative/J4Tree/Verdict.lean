module

public import Certificates.Data.CFSGNative.J4.F2
public import Certificates.Data.CFSGNative.J4Tree.Aff
public import Certificates.Data.CFSGNative.J4Tree.Index

public section

namespace CFSG.J4Tree.Native.Col

open CFSG.Sporadic.J4.Native CFSG.J4Tree.Native

set_option compiler.extract_closed false


@[expose] def unitV (i : Nat) : V2 := V2.zero.setBit i

@[expose] def lowBit (v : V2) : Nat :=
  go 112 0
where
  go : Nat → Nat → Nat
    | 0, _ => 112
    | fuel + 1, j => if v.testBit j then j else go fuel (j + 1)

@[expose] def elim (A : Array V2) : Array Nat × Array V2 × Array V2 × Array V2 := Id.run do
  let mut pivs : Array Nat := #[]
  let mut imgs : Array V2 := #[]
  let mut combs : Array V2 := #[]
  let mut kers : Array V2 := #[]
  for i in [0:112] do
    let mut img := (A[i]?.getD V2.zero).xor (unitV i)
    let mut comb := unitV i
    for t in [0:pivs.size] do
      if img.testBit pivs[t]! then
        img := img.xor imgs[t]!
        comb := comb.xor combs[t]!
    if img.beq V2.zero then
      kers := kers.push comb
    else
      let p := lowBit img
      for t in [0:imgs.size] do
        if imgs[t]!.testBit p then
          imgs := imgs.set! t (imgs[t]!.xor img)
          combs := combs.set! t (combs[t]!.xor comb)
      pivs := pivs.push p
      imgs := imgs.push img
      combs := combs.push comb
  return (pivs, imgs, combs, kers)


structure Tabs where
  uTab : Array (Array V2)
  kTab : Array (Array V2)
  gTab : Array (Array V2)
  giTab : Array (Array V2)
  idT : Array V2
  p0 : Array (Array V2)
  p0i : Array (Array V2)


@[expose] def xorSel : List Nat → Nat → Nat
  | [], _ => 0
  | o :: l, mask => (if mask % 2 = 1 then o else 0) ^^^ xorSel l (mask / 2)


structure VNode where
  k : Nat
  mode : Nat
  y : Nat
  o : List Nat
  e : String


end CFSG.J4Tree.Native.Col
