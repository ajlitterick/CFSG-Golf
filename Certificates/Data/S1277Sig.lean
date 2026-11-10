module

public import Std.Data.HashSet

public section

namespace Certificates.Data.S1277Sig

open Std

@[expose] def applyCols : List Nat → Nat → Nat
  | [], _ => 0
  | c :: cs, x => (if x % 2 = 1 then c else 0) ^^^ applyCols cs (x / 2)

@[expose] def compCols (a b : List Nat) : List Nat := b.map (applyCols a)

@[expose] def idCols (d : Nat) : List Nat := (List.range d).map fun i => 2 ^ i


end Certificates.Data.S1277Sig

end
