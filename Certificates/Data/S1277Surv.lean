module

public import Certificates.Data.S1277Cand
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

public section

namespace Certificates.Data.S1277Surv

open CFSG.Quasithin.H13.S127.Mod Certificates.Data.S1277Struct Certificates.Data.S1277Cand
  Certificates.Data.S1277Sig Certificates.Data.S1277Bfs Std

@[expose] def packC (cols : List Nat) : Nat := cols.foldr (fun c acc => c + 64 * acc) 0

@[expose] def unpackC (d x : Nat) : List Nat := (List.range d).map fun i => (x / 64 ^ i) % 64

@[expose] def app6 (x v : Nat) : Nat :=
  (if v % 2 = 1 then x % 64 else 0) ^^^ ((if (v / 2) % 2 = 1 then (x / 64) % 64 else 0) ^^^
  ((if (v / 4) % 2 = 1 then (x / 4096) % 64 else 0) ^^^
  ((if (v / 8) % 2 = 1 then (x / 262144) % 64 else 0) ^^^
  ((if (v / 16) % 2 = 1 then (x / 16777216) % 64 else 0) ^^^
  (if (v / 32) % 2 = 1 then (x / 1073741824) % 64 else 0)))))

@[expose] def mulSSpec (x y : Nat) : Nat := packC (compCols (unpackC 6 x) (unpackC 6 y))

@[expose] def mulS (x y : Nat) : Nat :=
  app6 x (y % 64) + 64 * (app6 x ((y / 64) % 64) + 64 * (app6 x ((y / 4096) % 64) +
    64 * (app6 x ((y / 262144) % 64) + 64 * (app6 x ((y / 16777216) % 64) +
      64 * app6 x ((y / 1073741824) % 64)))))

@[expose] def oneS : Nat := 1 + 64 * (2 + 64 * (4 + 64 * (8 + 64 * (16 + 64 * 32))))


end Certificates.Data.S1277Surv

end
