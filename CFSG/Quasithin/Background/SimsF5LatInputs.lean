module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListPermLat

public section

namespace CFSG.Quasithin.SimsF5Lat

open CFSG.QuasithinUnique.Vol2Native.A312L.PermLat CFSG.QuasithinUnique.Unc25K1.Six


@[ext] structure M6 where
  (a00 a01 a02 a03 a04 a05 : ℕ)
  (a10 a11 a12 a13 a14 a15 : ℕ)
  (a20 a21 a22 a23 a24 a25 : ℕ)
  (a30 a31 a32 a33 a34 a35 : ℕ)
  (a40 a41 a42 a43 a44 a45 : ℕ)
  (a50 a51 a52 a53 a54 a55 : ℕ)
  deriving DecidableEq, Hashable

namespace M6


@[expose, inline] def dot6 (a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5 : ℕ) : ℕ :=
  (a0 * b0 + a1 * b1 + a2 * b2 + a3 * b3 + a4 * b4 + a5 * b5) % 3

@[expose] def mul (x y : M6) : M6 where
  a00 := dot6 x.a00 x.a01 x.a02 x.a03 x.a04 x.a05 y.a00 y.a10 y.a20 y.a30 y.a40 y.a50
  a01 := dot6 x.a00 x.a01 x.a02 x.a03 x.a04 x.a05 y.a01 y.a11 y.a21 y.a31 y.a41 y.a51
  a02 := dot6 x.a00 x.a01 x.a02 x.a03 x.a04 x.a05 y.a02 y.a12 y.a22 y.a32 y.a42 y.a52
  a03 := dot6 x.a00 x.a01 x.a02 x.a03 x.a04 x.a05 y.a03 y.a13 y.a23 y.a33 y.a43 y.a53
  a04 := dot6 x.a00 x.a01 x.a02 x.a03 x.a04 x.a05 y.a04 y.a14 y.a24 y.a34 y.a44 y.a54
  a05 := dot6 x.a00 x.a01 x.a02 x.a03 x.a04 x.a05 y.a05 y.a15 y.a25 y.a35 y.a45 y.a55
  a10 := dot6 x.a10 x.a11 x.a12 x.a13 x.a14 x.a15 y.a00 y.a10 y.a20 y.a30 y.a40 y.a50
  a11 := dot6 x.a10 x.a11 x.a12 x.a13 x.a14 x.a15 y.a01 y.a11 y.a21 y.a31 y.a41 y.a51
  a12 := dot6 x.a10 x.a11 x.a12 x.a13 x.a14 x.a15 y.a02 y.a12 y.a22 y.a32 y.a42 y.a52
  a13 := dot6 x.a10 x.a11 x.a12 x.a13 x.a14 x.a15 y.a03 y.a13 y.a23 y.a33 y.a43 y.a53
  a14 := dot6 x.a10 x.a11 x.a12 x.a13 x.a14 x.a15 y.a04 y.a14 y.a24 y.a34 y.a44 y.a54
  a15 := dot6 x.a10 x.a11 x.a12 x.a13 x.a14 x.a15 y.a05 y.a15 y.a25 y.a35 y.a45 y.a55
  a20 := dot6 x.a20 x.a21 x.a22 x.a23 x.a24 x.a25 y.a00 y.a10 y.a20 y.a30 y.a40 y.a50
  a21 := dot6 x.a20 x.a21 x.a22 x.a23 x.a24 x.a25 y.a01 y.a11 y.a21 y.a31 y.a41 y.a51
  a22 := dot6 x.a20 x.a21 x.a22 x.a23 x.a24 x.a25 y.a02 y.a12 y.a22 y.a32 y.a42 y.a52
  a23 := dot6 x.a20 x.a21 x.a22 x.a23 x.a24 x.a25 y.a03 y.a13 y.a23 y.a33 y.a43 y.a53
  a24 := dot6 x.a20 x.a21 x.a22 x.a23 x.a24 x.a25 y.a04 y.a14 y.a24 y.a34 y.a44 y.a54
  a25 := dot6 x.a20 x.a21 x.a22 x.a23 x.a24 x.a25 y.a05 y.a15 y.a25 y.a35 y.a45 y.a55
  a30 := dot6 x.a30 x.a31 x.a32 x.a33 x.a34 x.a35 y.a00 y.a10 y.a20 y.a30 y.a40 y.a50
  a31 := dot6 x.a30 x.a31 x.a32 x.a33 x.a34 x.a35 y.a01 y.a11 y.a21 y.a31 y.a41 y.a51
  a32 := dot6 x.a30 x.a31 x.a32 x.a33 x.a34 x.a35 y.a02 y.a12 y.a22 y.a32 y.a42 y.a52
  a33 := dot6 x.a30 x.a31 x.a32 x.a33 x.a34 x.a35 y.a03 y.a13 y.a23 y.a33 y.a43 y.a53
  a34 := dot6 x.a30 x.a31 x.a32 x.a33 x.a34 x.a35 y.a04 y.a14 y.a24 y.a34 y.a44 y.a54
  a35 := dot6 x.a30 x.a31 x.a32 x.a33 x.a34 x.a35 y.a05 y.a15 y.a25 y.a35 y.a45 y.a55
  a40 := dot6 x.a40 x.a41 x.a42 x.a43 x.a44 x.a45 y.a00 y.a10 y.a20 y.a30 y.a40 y.a50
  a41 := dot6 x.a40 x.a41 x.a42 x.a43 x.a44 x.a45 y.a01 y.a11 y.a21 y.a31 y.a41 y.a51
  a42 := dot6 x.a40 x.a41 x.a42 x.a43 x.a44 x.a45 y.a02 y.a12 y.a22 y.a32 y.a42 y.a52
  a43 := dot6 x.a40 x.a41 x.a42 x.a43 x.a44 x.a45 y.a03 y.a13 y.a23 y.a33 y.a43 y.a53
  a44 := dot6 x.a40 x.a41 x.a42 x.a43 x.a44 x.a45 y.a04 y.a14 y.a24 y.a34 y.a44 y.a54
  a45 := dot6 x.a40 x.a41 x.a42 x.a43 x.a44 x.a45 y.a05 y.a15 y.a25 y.a35 y.a45 y.a55
  a50 := dot6 x.a50 x.a51 x.a52 x.a53 x.a54 x.a55 y.a00 y.a10 y.a20 y.a30 y.a40 y.a50
  a51 := dot6 x.a50 x.a51 x.a52 x.a53 x.a54 x.a55 y.a01 y.a11 y.a21 y.a31 y.a41 y.a51
  a52 := dot6 x.a50 x.a51 x.a52 x.a53 x.a54 x.a55 y.a02 y.a12 y.a22 y.a32 y.a42 y.a52
  a53 := dot6 x.a50 x.a51 x.a52 x.a53 x.a54 x.a55 y.a03 y.a13 y.a23 y.a33 y.a43 y.a53
  a54 := dot6 x.a50 x.a51 x.a52 x.a53 x.a54 x.a55 y.a04 y.a14 y.a24 y.a34 y.a44 y.a54
  a55 := dot6 x.a50 x.a51 x.a52 x.a53 x.a54 x.a55 y.a05 y.a15 y.a25 y.a35 y.a45 y.a55

@[expose] def one : M6 :=
  ⟨1, 0, 0, 0, 0, 0,
    0, 1, 0, 0, 0, 0,
    0, 0, 1, 0, 0, 0,
    0, 0, 0, 1, 0, 0,
    0, 0, 0, 0, 1, 0,
    0, 0, 0, 0, 0, 1⟩

instance : Mul M6 := ⟨mul⟩

instance : One M6 := ⟨one⟩


end M6


end CFSG.Quasithin.SimsF5Lat
