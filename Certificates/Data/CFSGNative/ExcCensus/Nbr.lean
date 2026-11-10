module

public import Certificates.Data.CFSGNative.ExcCensus.Check

public section

open Std

namespace CFSG.StandardType.GGQ2Frame.ExcRaw.Chk

set_option compiler.extract_closed false

inductive NbrW where
  | small (g : Nat) (L : List (Nat × Nat))
  | weyl (w : LinW) (L : List (Nat × Nat))
  deriving Inhabited

@[expose] def nbrWOK (T : Tabs) (m : Fin 6) (k : Nat) : NbrW → Bool
  | .small g L => decide (cardN (nroots m) g ≤ 2) && genOK T (nroots m) g k L
  | .weyl w L =>
    linOK T (nroots m) w && genOK T (nroots m) (nodeMask w fun _ => true) k L && notB2 m k

@[expose] def compsOK (T : Tabs) (r z : Nat) (ks : List Nat) : Bool :=
  ks.all (fun k => connN T r k && subN (trunc r k) z &&
      Nat.all r fun i _ => !k.testBit i || subN (T.adj[i]! &&& z) k) &&
    Nat.all r fun t _ => !z.testBit t || ks.any fun k => k.testBit t

structure NSearch where
  comps : Nat → List (Nat × NbrW)
  deriving Inhabited

@[expose] def nbrLineOK (T : Tabs) (m : Fin 6) (X : NSearch) (cv : Nat) : Bool :=
  compsOK T (nroots m) (T.zm[cv]!) ((X.comps cv).map Prod.fst) &&
    (X.comps cv).all fun e => nbrWOK T m e.1 e.2


end CFSG.StandardType.GGQ2Frame.ExcRaw.Chk

end
