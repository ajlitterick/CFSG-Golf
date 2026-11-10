module

public import Std.Data.HashMap

public section

namespace CFSG.CGT.Stroth77.GL5

set_option compiler.extract_closed false

@[expose] def N : Nat := 33554432

@[expose] def r0 (c : Nat) : Nat := c % 32
@[expose] def r1 (c : Nat) : Nat := c / 32 % 32
@[expose] def r2 (c : Nat) : Nat := c / 1024 % 32
@[expose] def r3 (c : Nat) : Nat := c / 32768 % 32
@[expose] def r4 (c : Nat) : Nat := c / 1048576 % 32

@[expose] def ofRows (a b c d e : Nat) : Nat := a + 32 * b + 1024 * c + 32768 * d + 1048576 * e

@[expose] def vm5 (v m0 m1 m2 m3 m4 : Nat) : Nat :=
  (if v.testBit 0 then m0 else 0) ^^^ (if v.testBit 1 then m1 else 0) ^^^
    (if v.testBit 2 then m2 else 0) ^^^ (if v.testBit 3 then m3 else 0) ^^^
    (if v.testBit 4 then m4 else 0)

@[expose] def vm (v c : Nat) : Nat := vm5 v (r0 c) (r1 c) (r2 c) (r3 c) (r4 c)

@[expose] def mulC (a b : Nat) : Nat :=
  let a0 := r0 a
  let a1 := r1 a
  let a2 := r2 a
  let a3 := r3 a
  let a4 := r4 a
  ofRows (vm5 (r0 b) a0 a1 a2 a3 a4) (vm5 (r1 b) a0 a1 a2 a3 a4) (vm5 (r2 b) a0 a1 a2 a3 a4)
    (vm5 (r3 b) a0 a1 a2 a3 a4) (vm5 (r4 b) a0 a1 a2 a3 a4)

@[expose] def idC : Nat := 17043521
@[expose] def uvC : Nat := 20224065
@[expose] def tC : Nat := 18191425
@[expose] def uC : Nat := 16916514
@[expose] def rhoC : Nat := 17178722

@[expose] def genC (i : Nat) : Nat :=
  if i = 0 then uvC else if i = 1 then tC else if i = 2 then uC else if i = 3 then rhoC else idC

@[expose] def powC (h : Nat) : Nat → Nat
  | 0 => idC
  | k + 1 => mulC h (powC h k)

@[expose] def evalList : List Nat → Nat
  | [] => idC
  | i :: l => mulC (genC i) (evalList l)

@[expose] def x0Words : Array (List Nat) :=
  #[[], [0], [1], [2], [3], [0, 1], [0, 2], [0, 3], [1, 2], [1, 3], [2, 1], [2, 3], [3, 1], [3, 2],
    [3, 3], [0, 2, 3], [0, 3, 2], [0, 3, 3], [1, 2, 3], [1, 3, 2], [1, 3, 3], [2, 1, 3], [3, 1, 2],
    [3, 1, 3]]


@[expose] def vCodes : List Nat := [idC, uvC, tC, 19209281]

@[expose] def dCodes : List Nat :=
  [16916514, 17043521, 18000930, 18191425, 19114018, 19209281, 20128802, 20224065]

@[expose] def span5 (a b c d e : Nat) : Bool :=
  let ab_ := a ^^^ b
  let ac_ := a ^^^ c
  let bc_ := b ^^^ c
  let ad_ := a ^^^ d
  let bd_ := b ^^^ d
  let cd_ := c ^^^ d
  let ae_ := a ^^^ e
  let be_ := b ^^^ e
  let ce_ := c ^^^ e
  let de_ := d ^^^ e
  let abc_ := ab_ ^^^ c
  let abd_ := ab_ ^^^ d
  let acd_ := ac_ ^^^ d
  let bcd_ := bc_ ^^^ d
  let abe_ := ab_ ^^^ e
  let ace_ := ac_ ^^^ e
  let bce_ := bc_ ^^^ e
  let ade_ := ad_ ^^^ e
  let bde_ := bd_ ^^^ e
  let cde_ := cd_ ^^^ e
  let abcd_ := abc_ ^^^ d
  let abce_ := abc_ ^^^ e
  let abde_ := abd_ ^^^ e
  let acde_ := acd_ ^^^ e
  let bcde_ := bcd_ ^^^ e
  let abcde_ := abcd_ ^^^ e
  a != 0 && b != 0 && ab_ != 0 && c != 0 && ac_ != 0 && bc_ != 0 && abc_ != 0 && d != 0 &&
    ad_ != 0 && bd_ != 0 && abd_ != 0 && cd_ != 0 && acd_ != 0 && bcd_ != 0 && abcd_ != 0 &&
    e != 0 && ae_ != 0 && be_ != 0 && abe_ != 0 && ce_ != 0 && ace_ != 0 && bce_ != 0 &&
    abce_ != 0 && de_ != 0 && ade_ != 0 && bde_ != 0 && abde_ != 0 && cde_ != 0 && acde_ != 0 &&
    bcde_ != 0 && abcde_ != 0

@[expose] def nonsing (c : Nat) : Bool := span5 (r0 c) (r1 c) (r2 c) (r3 c) (r4 c)

@[expose] def stabW4 (c : Nat) : Bool :=
  decide (r0 c < 16) && decide (r1 c < 16) && decide (r2 c < 16) && decide (r3 c < 16)

@[expose] def good (h : Nat) : Bool :=
  mulC h uvC == mulC uvC h && mulC h tC == mulC tC h && !vCodes.contains h

@[expose] def normD (c : Nat) : Bool :=
  [uvC, tC, uC].all fun d => dCodes.any fun d' => mulC c d == mulC d' c

@[expose] def normV (c : Nat) : Bool :=
  [uvC, tC].all fun d => vCodes.any fun d' => mulC c d == mulC d' c


end CFSG.CGT.Stroth77.GL5
