module

public import Certificates.Data.CFSGNative.Co1.CoTwoChain

public section

namespace CFSG.Sporadic.Co1.U6OddNative

open CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Th.Native CFSG.Sporadic.Co1.OddNative
  CFSG.Sporadic.Co1.CoTwoNative

@[expose] def xcN : List Nat → Nat → Nat
  | [], _ => 0
  | x :: xs, m => (if m % 2 = 1 then x else 0) ^^^ xcN xs (m / 2)


structure PrimeData where
  p : Nat
  g : Nat
  base : List Nat
  lv : List (List Nat)
  sz : List Nat
  final : List Nat
  b : List Nat
  t : Nat
  k : Nat

@[expose] def fixAll (rr : Nat → Array Nat) (xs ss : List Nat) : Bool :=
  ss.all fun s => xs.all fun x => fixOK rr x s

@[expose] def chainCheck (rr : Nat → Array Nat) (u₁ u₂ : Nat) (pd : PrimeData) : Bool :=
  decide (pd.lv.length = pd.base.length) && decide (pd.sz.length = pd.base.length) &&
    (List.range pd.base.length).all (fun i =>
      fixAll rr (u₁ :: u₂ :: pd.base.take i) (pd.lv.getD i []) &&
        decide (pd.sz.getD i 0 ≤ treeSize rr (pd.lv.getD i []) (pd.base.getD i 0))) &&
    fixAll rr (u₁ :: u₂ :: pd.base) pd.final &&
      decide (9196830720 ≤ ((List.range pd.base.length).map fun i => pd.sz.getD i 0).prod * pd.k)


end CFSG.Sporadic.Co1.U6OddNative
