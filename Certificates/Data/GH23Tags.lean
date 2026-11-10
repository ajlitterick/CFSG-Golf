module

public import Certificates.Data.GH23Lat

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.GH23Data

set_option compiler.extract_closed false

@[expose] def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n


@[expose] def carmRels (imgs : List Nat) : Bool :=
  (List.range imgs.length).all fun i =>
    mulC (mulC (imgs.getD i 0) (imgs.getD i 0)) (imgs.getD i 0) == oneC &&
      (List.range imgs.length).all fun j =>
        i == j || mulC (mulC (imgs.getD i 0) (imgs.getD j 0))
          (mulC (imgs.getD i 0) (imgs.getD j 0)) == oneC

@[expose] def coxRels (imgs : List Nat) : Bool :=
  (List.range imgs.length).all (fun i => mulC (imgs.getD i 0) (imgs.getD i 0) == oneC) &&
  (List.range imgs.length).all (fun i =>
    decide (imgs.length ≤ i + 1) ||
      mulC (mulC (imgs.getD i 0) (imgs.getD (i + 1) 0)) (imgs.getD i 0) ==
        mulC (mulC (imgs.getD (i + 1) 0) (imgs.getD i 0)) (imgs.getD (i + 1) 0)) &&
  (List.range imgs.length).all fun i => (List.range imgs.length).all fun j =>
    decide (j < i + 2) ||
      mulC (imgs.getD i 0) (imgs.getD j 0) == mulC (imgs.getD j 0) (imgs.getD i 0)


end CFSG.OddStandard.SmallF3.HarrisU33.GH23Data
