module

public import CFSG.Fischer.F4

public section

namespace CFSG.RankThree.PartTwo.Sec10.KS1012GL34.Light

open CFSG.Fischer

structure M3 where
  a00 : F4
  a01 : F4
  a02 : F4
  a10 : F4
  a11 : F4
  a12 : F4
  a20 : F4
  a21 : F4
  a22 : F4
deriving DecidableEq

structure V3 where
  x : F4
  y : F4
  z : F4
deriving DecidableEq

@[expose] def oneL : M3 := ⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩

@[expose] def XdL : M3 := ⟨1, 0, 0, 0, ⟨3⟩, 0, 0, 0, ⟨2⟩⟩

@[expose] def ZsL : M3 := ⟨⟨2⟩, 0, 0, 0, ⟨2⟩, 0, 0, 0, ⟨2⟩⟩

@[expose] def WmL (μ : F4) : M3 := ⟨0, 0, μ, 1, 0, 0, 0, 1, 0⟩

@[expose] def E01L : M3 := ⟨1, 1, 0, 0, 1, 0, 0, 0, 1⟩
@[expose] def E02L : M3 := ⟨1, 0, 1, 0, 1, 0, 0, 0, 1⟩
@[expose] def E10L : M3 := ⟨1, 0, 0, 1, 1, 0, 0, 0, 1⟩
@[expose] def E12L : M3 := ⟨1, 0, 0, 0, 1, 1, 0, 0, 1⟩
@[expose] def E20L : M3 := ⟨1, 0, 0, 0, 1, 0, 1, 0, 1⟩
@[expose] def E21L : M3 := ⟨1, 0, 0, 0, 1, 0, 0, 1, 1⟩

@[expose] def mulL (A B : M3) : M3 :=
  ⟨A.a00 * B.a00 + A.a01 * B.a10 + A.a02 * B.a20, A.a00 * B.a01 + A.a01 * B.a11 + A.a02 * B.a21,
    A.a00 * B.a02 + A.a01 * B.a12 + A.a02 * B.a22,
    A.a10 * B.a00 + A.a11 * B.a10 + A.a12 * B.a20, A.a10 * B.a01 + A.a11 * B.a11 + A.a12 * B.a21,
    A.a10 * B.a02 + A.a11 * B.a12 + A.a12 * B.a22,
    A.a20 * B.a00 + A.a21 * B.a10 + A.a22 * B.a20, A.a20 * B.a01 + A.a21 * B.a11 + A.a22 * B.a21,
    A.a20 * B.a02 + A.a21 * B.a12 + A.a22 * B.a22⟩

@[expose] def mulV (A : M3) (v : V3) : V3 :=
  ⟨A.a00 * v.x + A.a01 * v.y + A.a02 * v.z, A.a10 * v.x + A.a11 * v.y + A.a12 * v.z,
    A.a20 * v.x + A.a21 * v.y + A.a22 * v.z⟩

@[expose] def smulV (c : F4) (v : V3) : V3 := ⟨c * v.x, c * v.y, c * v.z⟩

@[expose] def detL (A : M3) : F4 :=
  A.a00 * (A.a11 * A.a22 - A.a12 * A.a21) - A.a01 * (A.a10 * A.a22 - A.a12 * A.a20) +
    A.a02 * (A.a10 * A.a21 - A.a11 * A.a20)

@[expose] def allF4 : List F4 := [0, 1, F4.ω, ⟨3⟩]

@[expose] def allM3L (_ : Unit := ()) : List M3 :=
  allF4.flatMap fun a00 => allF4.flatMap fun a01 => allF4.flatMap fun a02 =>
  allF4.flatMap fun a10 => allF4.flatMap fun a11 => allF4.flatMap fun a12 =>
  allF4.flatMap fun a20 => allF4.flatMap fun a21 => allF4.map fun a22 =>
    (⟨a00, a01, a02, a10, a11, a12, a20, a21, a22⟩ : M3)

@[expose] def NZL : List F4 := [1, F4.ω, ⟨3⟩]

@[expose] def omegaL : Nat → List V3
  | 0 => [⟨1, 1, 1⟩, ⟨1, ⟨3⟩, ⟨3⟩⟩, ⟨1, F4.ω, ⟨3⟩⟩, ⟨1, 1, F4.ω⟩, ⟨1, ⟨3⟩, F4.ω⟩, ⟨1, F4.ω, 1⟩]
  | 1 => [⟨0, 0, 1⟩, ⟨1, F4.ω, F4.ω⟩, ⟨0, 1, 0⟩, ⟨1, 0, 0⟩, ⟨1, 1, ⟨3⟩⟩, ⟨1, ⟨3⟩, 1⟩]
  | 2 => [⟨0, 0, 1⟩, ⟨1, ⟨3⟩, ⟨3⟩⟩, ⟨1, 0, 0⟩, ⟨1, F4.ω, 1⟩, ⟨1, 1, F4.ω⟩, ⟨0, 1, 0⟩]
  | 3 => [⟨1, 1, 1⟩, ⟨1, ⟨3⟩, 1⟩, ⟨1, 1, ⟨3⟩⟩, ⟨1, F4.ω, ⟨3⟩⟩, ⟨1, ⟨3⟩, F4.ω⟩, ⟨1, F4.ω, F4.ω⟩]
  | 4 => [⟨1, 1, F4.ω⟩, ⟨1, ⟨3⟩, ⟨3⟩⟩, ⟨1, F4.ω, 1⟩, ⟨1, 1, ⟨3⟩⟩, ⟨1, F4.ω, F4.ω⟩, ⟨1, ⟨3⟩, 1⟩]
  | 5 => [⟨0, 0, 1⟩, ⟨1, F4.ω, ⟨3⟩⟩, ⟨1, ⟨3⟩, F4.ω⟩, ⟨1, 1, 1⟩, ⟨1, 0, 0⟩, ⟨0, 1, 0⟩]
  | _ => []

@[expose] def stabOf (Om Av : List V3) : Bool :=
  Av.all fun x => Om.any fun u => NZL.any fun c => x == smulV c u

@[expose] def stabLn (k : Nat) (A : M3) : Bool :=
  stabOf (omegaL k) ((omegaL k).map (mulV A))


@[expose] def gensT3 (μ : F4) (A : M3) : List M3 :=
  [XdL, mulL XdL XdL, WmL μ, mulL (WmL μ) (WmL μ), ZsL, mulL ZsL ZsL, A]


end CFSG.RankThree.PartTwo.Sec10.KS1012GL34.Light

end
