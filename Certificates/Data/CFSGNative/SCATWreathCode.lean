module

public import Certificates.Data.CFSGNative.SCATWreathData

public section

namespace CFSG.SCATWreath

@[expose] def mCol (m j : Nat) : Nat := (m >>> (6 * j)) &&& 63

@[expose] def mSel (v j c : Nat) : Nat := if v.testBit j then c else 0

@[expose] def mAct (m v : Nat) : Nat :=
  mSel v 0 (mCol m 0) ^^^ mSel v 1 (mCol m 1) ^^^ mSel v 2 (mCol m 2) ^^^ mSel v 3 (mCol m 3) ^^^
    mSel v 4 (mCol m 4) ^^^ mSel v 5 (mCol m 5)

@[expose] def mPack (c₀ c₁ c₂ c₃ c₄ c₅ : Nat) : Nat :=
  c₀ + 64 * (c₁ + 64 * (c₂ + 64 * (c₃ + 64 * (c₄ + 64 * c₅))))

@[expose] def mMul (a b : Nat) : Nat :=
  mPack (mAct a (mCol b 0)) (mAct a (mCol b 1)) (mAct a (mCol b 2)) (mAct a (mCol b 3))
    (mAct a (mCol b 4)) (mAct a (mCol b 5))

@[expose] def smulTab (L : List Nat) : Array Nat :=
  let A := L.toArray
  Array.ofFn (n := 128 * 128) fun ij => L.idxOf (mMul A[ij.1 / 128]! A[ij.1 % 128]!)

@[expose] def actTab (L : List Nat) : Array Nat :=
  let A := L.toArray
  Array.ofFn (n := 128 * 64) fun iv => mAct A[iv.1 / 64]! (iv.1 % 64)

@[expose] def wMul (sm ac : Array Nat) (a b : Nat) : Nat :=
  64 * sm[a / 64 * 128 + b / 64]! + (a % 64 ^^^ ac[a / 64 * 64 + b % 64]!)


@[expose] def pw (mul : Nat → Nat → Nat) (c : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => mul c (pw mul c k)


@[expose] def invOK (n : Nat) (mul : Nat → Nat → Nat) (inv : Array Nat) : Bool :=
  (List.range n).all fun c => inv[c]! < n && mul c inv[c]! == 0


@[expose] def labOK (n : Nat) (mul : Nat → Nat → Nat) (gens ginv lab reps wit : Array Nat)
    (dom : List Nat) : Bool :=
  (List.range gens.size).all (fun i => gens[i]! < n && ginv[i]! < n &&
    mul gens[i]! ginv[i]! == 0) && reps.all (· < n) &&
  dom.all fun c => lab[c]! < reps.size && wit[c]! < n &&
    mul c wit[c]! == mul wit[c]! reps[lab[c]!]! &&
    (List.range gens.size).all fun i => lab[mul (mul gens[i]! c) ginv[i]!]! == lab[c]!


@[expose] def invols (n : Nat) (mul : Nat → Nat → Nat) : List Nat :=
  (List.range n).filter fun c => c != 0 && mul c c == 0

@[expose] def cntC (mul : Nat → Nat → Nat) (dom : List Nat) (r : Nat) : Nat :=
  (dom.filter fun c => mul r c == mul c r).length


end CFSG.SCATWreath
