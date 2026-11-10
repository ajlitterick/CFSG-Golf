module

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering2119S

structure V4C where
  a : Nat
  b : Nat
  c : Nat
  d : Nat
deriving DecidableEq

structure M4C where
  m00 : Nat
  m01 : Nat
  m02 : Nat
  m03 : Nat
  m10 : Nat
  m11 : Nat
  m12 : Nat
  m13 : Nat
  m20 : Nat
  m21 : Nat
  m22 : Nat
  m23 : Nat
  m30 : Nat
  m31 : Nat
  m32 : Nat
  m33 : Nat
deriving DecidableEq

@[expose] def M4C.one : M4C :=
  ⟨1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1⟩

@[expose] def M4C.mul (A B : M4C) : M4C where
  m00 := (A.m00 * B.m00 + A.m01 * B.m10 + A.m02 * B.m20 + A.m03 * B.m30) % 3
  m01 := (A.m00 * B.m01 + A.m01 * B.m11 + A.m02 * B.m21 + A.m03 * B.m31) % 3
  m02 := (A.m00 * B.m02 + A.m01 * B.m12 + A.m02 * B.m22 + A.m03 * B.m32) % 3
  m03 := (A.m00 * B.m03 + A.m01 * B.m13 + A.m02 * B.m23 + A.m03 * B.m33) % 3
  m10 := (A.m10 * B.m00 + A.m11 * B.m10 + A.m12 * B.m20 + A.m13 * B.m30) % 3
  m11 := (A.m10 * B.m01 + A.m11 * B.m11 + A.m12 * B.m21 + A.m13 * B.m31) % 3
  m12 := (A.m10 * B.m02 + A.m11 * B.m12 + A.m12 * B.m22 + A.m13 * B.m32) % 3
  m13 := (A.m10 * B.m03 + A.m11 * B.m13 + A.m12 * B.m23 + A.m13 * B.m33) % 3
  m20 := (A.m20 * B.m00 + A.m21 * B.m10 + A.m22 * B.m20 + A.m23 * B.m30) % 3
  m21 := (A.m20 * B.m01 + A.m21 * B.m11 + A.m22 * B.m21 + A.m23 * B.m31) % 3
  m22 := (A.m20 * B.m02 + A.m21 * B.m12 + A.m22 * B.m22 + A.m23 * B.m32) % 3
  m23 := (A.m20 * B.m03 + A.m21 * B.m13 + A.m22 * B.m23 + A.m23 * B.m33) % 3
  m30 := (A.m30 * B.m00 + A.m31 * B.m10 + A.m32 * B.m20 + A.m33 * B.m30) % 3
  m31 := (A.m30 * B.m01 + A.m31 * B.m11 + A.m32 * B.m21 + A.m33 * B.m31) % 3
  m32 := (A.m30 * B.m02 + A.m31 * B.m12 + A.m32 * B.m22 + A.m33 * B.m32) % 3
  m33 := (A.m30 * B.m03 + A.m31 * B.m13 + A.m32 * B.m23 + A.m33 * B.m33) % 3

@[expose] def M4C.mv (A : M4C) (v : V4C) : V4C :=
  ⟨(A.m00 * v.a + A.m01 * v.b + A.m02 * v.c + A.m03 * v.d) % 3,
    (A.m10 * v.a + A.m11 * v.b + A.m12 * v.c + A.m13 * v.d) % 3,
    (A.m20 * v.a + A.m21 * v.b + A.m22 * v.c + A.m23 * v.d) % 3,
    (A.m30 * v.a + A.m31 * v.b + A.m32 * v.c + A.m33 * v.d) % 3⟩

@[expose] def V4C.om (x y : V4C) : Nat :=
  (x.a * y.c + 2 * (x.c * y.a) + x.b * y.d + 2 * (x.d * y.b)) % 3

@[expose] def V4C.add (x y : V4C) : V4C :=
  ⟨(x.a + y.a) % 3, (x.b + y.b) % 3, (x.c + y.c) % 3, (x.d + y.d) % 3⟩

@[expose] def V4C.smul (k : Nat) (x : V4C) : V4C :=
  ⟨(k * x.a) % 3, (k * x.b) % 3, (k * x.c) % 3, (k * x.d) % 3⟩

@[expose] def V4C.neg (x : V4C) : V4C := x.smul 2


@[expose] def allVecs : List V4C :=
  (List.range 3).flatMap fun a => (List.range 3).flatMap fun b =>
    (List.range 3).flatMap fun c => (List.range 3).map fun d => ⟨a, b, c, d⟩


@[expose] def lineC (L : Nat) : V4C :=
  match L with
  | 0 => ⟨1, 0, 0, 0⟩
  | 1 => ⟨0, 1, 0, 0⟩
  | 2 => ⟨1, 1, 0, 0⟩
  | _ => ⟨1, 2, 0, 0⟩


@[expose] def sameCyc (A B : M4C) : Bool := B == A || B == A.mul A

@[expose] def conclC (X0 X1 X2 X3 : M4C) : Bool :=
  allVecs.all (fun v => ((X1.mv v == v) == (X0.mv v == v)) && ((X2.mv v == v) == (X0.mv v == v)) &&
    ((X3.mv v == v) == (X0.mv v == v))) &&
  ((sameCyc X0 X1 && sameCyc X2 X3 && !sameCyc X0 X2) ||
   (sameCyc X0 X2 && sameCyc X1 X3 && !sameCyc X0 X1) ||
   (sameCyc X0 X3 && sameCyc X1 X2 && !sameCyc X0 X1))

@[expose] def uC (a b c : Nat) : M4C := ⟨1, 0, a, b, 0, 1, b, c, 0, 0, 1, 0, 0, 0, 0, 1⟩


end CFSG.RankThree.PartTwo.Sec21.Hering2119S
