module

public import CFSG.Fischer.F4
public import Mathlib.Algebra.Order.Ring.Star

public section

namespace CFSG.Quasithin.H13.Ch9.L34Q

open CFSG.Fischer

abbrev M2 : Type := Matrix (Fin 2) (Fin 2) F4

@[expose] def f4 (n : ℕ) : F4 := ⟨⟨n % 4, Nat.mod_lt _ (by norm_num)⟩⟩

@[expose] def code (X : M2) : ℕ :=
  (X 0 0).code.val + 4 * ((X 0 1).code.val + 4 * ((X 1 0).code.val + 4 * (X 1 1).code.val))

@[expose] def decode (c : ℕ) : M2 := !![f4 c, f4 (c / 4); f4 (c / 16), f4 (c / 64)]

@[expose] def frob (x : F4) : F4 := x * x

@[expose] def gmap (A B : M2) (s t : Bool) (X : M2) : M2 :=
  A * (if s then Matrix.transpose (if t then X.map frob else X) else
    (if t then X.map frob else X)) * Matrix.transpose B

structure Par where
  A : M2
  B : M2
  s : Bool
  t : Bool

@[expose] def allF4 : List F4 := [f4 0, f4 1, f4 2, f4 3]

@[expose] def nzF4 : List F4 := [f4 1, f4 2, f4 3]

@[expose] def params : List Par :=
  allF4.flatMap fun a => nzF4.flatMap fun a' => nzF4.flatMap fun b1 => allF4.flatMap fun b =>
    nzF4.flatMap fun b2 => [false, true].flatMap fun s => [false, true].map fun t =>
      ⟨!![1, a; 0, a'], !![b1, b; 0, b2], s, t⟩

@[expose] def act (p : Par) (v : ℕ) : ℕ := code (gmap p.A p.B p.s p.t (decode v))

@[expose] def isInvAct (p : Par) : Bool :=
  (List.range 8).all fun k => act p (act p (2 ^ k)) == 2 ^ k


@[expose] def maskOf (P : ℕ → Bool) : ℕ :=
  (List.range 256).foldl (fun m v => if P v then m ||| (1 <<< v) else m) 0

@[expose] def fixM (p : Par) : ℕ := maskOf fun v => act p v == v

@[expose] def comM (p : Par) : ℕ :=
  (List.range 256).foldl (fun m v => m ||| (1 <<< code (gmap p.A p.B p.s p.t (decode v) +
    decode v))) 0

@[expose] def FULL : ℕ := maskOf fun _ => true

@[expose] def lo (k : ℕ) : ℕ := maskOf fun v => !v.testBit k

@[expose] def loTab : Array ℕ := #[lo 0, lo 1, lo 2, lo 3, lo 4, lo 5, lo 6, lo 7]

@[expose] def tr1 (m k : ℕ) : ℕ :=
  ((m &&& loTab.getD k 0) <<< (2 ^ k)) ||| ((m >>> (2 ^ k)) &&& loTab.getD k 0)

@[expose] def transB (m w : ℕ) : ℕ → ℕ
  | 0 => m
  | j + 1 => if w.testBit j then tr1 (transB m w j) j else transB m w j

@[expose] def sumOne (m w : ℕ) : ℕ := (m ||| transB m w 8) &&& FULL

@[expose] def basisOf (m : ℕ) : List ℕ :=
  ((List.range 256).foldl (fun (acc : List ℕ × ℕ) v =>
    if m.testBit v && !acc.2.testBit v then (v :: acc.1, sumOne acc.2 v) else acc) ([], 1)).1

structure IData where
  fix : ℕ
  com : ℕ
  bas : List ℕ

@[expose] def dataOf (p : Par) : IData := let c := comM p; ⟨fixM p, c, basisOf c⟩


@[expose] def popcount (m : ℕ) : ℕ := (List.range 256).countP fun v => m.testBit v


@[expose] def elat (W : ℕ) (d : IData) : Bool := (W &&& d.fix == W) && (d.com &&& W == d.com)


end CFSG.Quasithin.H13.Ch9.L34Q
