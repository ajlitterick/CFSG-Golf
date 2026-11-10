module

public import Certificates.Data.CFSGNative.MonsterB.Max2Pinned

public section

namespace CFSG.Monster.B.Primes.Native

open CFSG.Monster.B.Bin

set_option compiler.extract_closed false

inductive Ins where
  | mu (i j k : Nat)
  | iv (i k : Nat)
  | pwr (e i k : Nat)
deriving Inhabited

@[expose] def Ins.lt (N : Nat) : Ins → Bool
  | .mu i j k => decide (i < N) && decide (j < N) && decide (k < N)
  | .iv i k => decide (i < N) && decide (k < N)
  | .pwr _ i k => decide (i < N) && decide (k < N)

@[expose] def regStep (n : Nat) (st : Array Mat × Bool) : Ins → Array Mat × Bool
  | .mu i j k => (st.1.set! k (mulP n (st.1.getD i #[]) (st.1.getD j #[])), st.2)
  | .iv i k =>
    let X := st.1.getD i #[]
    let Y := invM n X
    (st.1.set! k Y, st.2 && mulP n X Y == idMat n)
  | .pwr e i k => (st.1.set! k (powM n (st.1.getD i #[]) e), st.2)

@[expose] def regsInit (n N : Nat) (A B : Mat) : Array Mat :=
  Array.ofFn (n := N) fun i => if i.val = 1 then A else if i.val = 2 then B else idMat n

@[expose] def regRun (n N : Nat) (prog : List Ins) (A B : Mat) : Array Mat × Bool :=
  prog.foldl (regStep n) (regsInit n N A B, true)

@[expose] def fiveProg (_ : Unit := ()) : List Ins :=
  [.mu 1 2 3, .mu 3 2 4, .mu 3 3 5, .mu 5 5 3, .mu 3 4 12, .mu 12 12 3, .mu 12 3 4, .mu 4 4 5,
    .mu 5 5 3, .mu 3 3 10, .mu 1 10 3, .mu 3 3 11, .mu 11 12 3, .mu 3 12 4, .mu 3 3 5, .mu 4 3 6,
    .mu 5 6 7, .mu 7 7 8, .mu 7 8 9, .mu 8 9 13, .mu 3 4 5, .mu 5 5 6, .mu 12 6 7, .mu 7 7 8,
    .mu 8 8 9, .mu 4 6 7, .mu 7 5 3, .iv 3 4, .mu 4 9 5, .mu 5 3 14, .mu 13 14 3, .mu 3 14 4,
    .mu 4 14 5, .mu 5 14 6, .pwr 3 4 15, .mu 5 5 4, .mu 3 3 5, .mu 5 4 7, .pwr 5 7 4, .pwr 20 6 5,
    .pwr 6 3 6, .mu 5 6 3, .iv 3 5, .mu 5 4 6, .mu 6 3 16, .mu 15 16 3, .mu 3 16 4, .mu 3 4 5,
    .mu 3 5 6, .pwr 6 6 7, .iv 15 8, .mu 7 8 9, .mu 7 15 6, .mu 9 6 5, .mu 5 5 6, .mu 15 6 17,
    .iv 16 8, .mu 7 8 9, .pwr 3 7 5, .mu 5 16 6, .mu 9 6 5, .mu 5 5 6, .mu 16 6 18, .mu 17 18 3,
    .mu 3 18 4, .mu 3 4 5, .mu 3 5 6, .pwr 15 6 7, .mu 7 10 19, .mu 1 19 3, .pwr 17 3 20,
    .pwr 6 6 21, .mu 20 21 3, .pwr 4 3 4, .iv 4 5, .mu 21 5 6, .mu 21 4 7, .mu 6 7 8, .mu 8 8 7,
    .mu 4 7 5, .iv 5 4, .mu 21 4 6, .mu 21 5 7, .mu 6 7 8, .mu 8 8 7, .mu 5 7 1, .mu 17 18 2]

@[expose] def threeProg (_ : Unit := ()) : List Ins :=
  [.mu 1 2 3, .mu 3 2 4, .mu 3 3 5, .mu 5 5 3, .mu 3 4 12, .mu 12 12 3, .mu 12 3 4, .mu 4 4 5,
    .mu 5 5 3, .mu 3 3 4, .mu 1 4 3, .mu 3 3 11, .mu 11 12 3, .mu 3 12 4, .mu 3 3 5, .mu 4 3 6,
    .mu 5 6 7, .mu 7 7 8, .mu 7 8 9, .mu 8 9 13, .mu 3 4 5, .mu 5 5 6, .mu 12 6 7, .mu 7 7 8,
    .mu 8 8 9, .mu 4 6 7, .mu 7 5 3, .iv 3 4, .mu 4 9 5, .mu 5 3 14, .mu 13 14 3, .mu 3 14 4,
    .mu 3 4 5, .mu 3 5 6, .mu 6 3 7, .mu 7 4 8, .mu 3 8 9, .mu 5 8 4, .pwr 5 4 15, .pwr 3 5 4,
    .pwr 17 6 5, .pwr 24 9 6, .mu 5 6 7, .iv 7 8, .mu 8 4 6, .mu 6 7 16, .mu 15 16 3, .pwr 10 3 4,
    .iv 15 5, .mu 15 4 6, .iv 4 7, .mu 7 15 8, .mu 6 5 9, .mu 9 8 17, .iv 16 5, .mu 16 4 6,
    .mu 7 16 8, .mu 6 5 9, .mu 9 8 2, .mu 17 2 3, .pwr 15 3 4, .pwr 24 12 5, .mu 4 5 6, .mu 1 6 7,
    .pwr 26 7 1, .pwr 5 3 5, .mu 5 5 3, .mu 1 3 4, .mu 4 4 5, .iv 5 6, .mu 5 3 7, .mu 6 3 8,
    .mu 7 8 9, .mu 9 5 4, .iv 4 6, .mu 4 3 7, .mu 6 3 8, .mu 7 8 9, .mu 9 4 5, .mu 17 5 1]


@[expose] def word7 : String := "ababbabbab"

@[expose] def word17 : String := "ababbabbababababababb"

@[expose] def word19 : String := "ababbabbababababababbabababb"

@[expose] def word31 : String := "ababbabbababababababbabababbabababb"

@[expose] def word47 : String :=
  "ababbabbababababababbabababbabababbababbabbababababbabbababbabbab"

@[expose] def word13 : String :=
  "ababbabbababababababbabababbabababbababbabbababababbabbababbabbababbabababb"

@[expose] def ordOK (n p : Nat) (X : Mat) : Bool := powM n X p == idMat n && neM n X (idMat n)


@[expose] def mulTab (n : Nat) (P : Mat) (Z : List Mat) (c : Nat) : Mat :=
  if c = 0 then P else mulP n P (Z.getD c #[])


@[expose] def conjM (n : Nat) (Y b bi : Mat) : Mat := mulP n (mulP n bi Y) b


end CFSG.Monster.B.Primes.Native
