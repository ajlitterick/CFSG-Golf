module

public import Certificates.Data.CFSGNative.HS.SmallF2
public import Std.Data.HashMap

public section

namespace CFSG.Quasithin.H13.J4.Native

open CFSG.Sporadic.SmallF2.Native

abbrev Pr12 : Type := Array Nat × Array Nat

@[expose] def pr12One (_ : Unit := ()) : Pr12 := (idRows 12, idRows 12)

@[expose] def pr12Mul (x y : Pr12) : Pr12 := (mulRows 12 x.1 y.1, mulRows 12 y.2 x.2)

@[expose] def pr12Inv (x : Pr12) : Pr12 := (x.2, x.1)

@[expose] def pr12Letter (gs : Array Pr12) (l : Int) : Pr12 :=
  if 0 < l then gs[l.toNat - 1]?.getD pr12One else pr12Inv (gs[(-l).toNat - 1]?.getD pr12One)

@[expose] def pr12Word (gs : Array Pr12) (w : List Int) : Pr12 :=
  w.foldl (fun acc l => pr12Mul acc (pr12Letter gs l)) pr12One


structure Lvl12 where
  gens : Array Pr12
  cols : Array (Array Nat)
  base : Nat
  paths : Array (List Nat)
  pts : Array Nat

instance : Inhabited Lvl12 := ⟨⟨#[], #[], 0, #[[]], #[0]⟩⟩


end CFSG.Quasithin.H13.J4.Native
