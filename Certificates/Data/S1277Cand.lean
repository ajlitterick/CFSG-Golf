module

public import Certificates.Data.S1277Struct
public import Certificates.Data.S1277Sig

public section

namespace Certificates.Data.S1277Cand

open CFSG.Quasithin.H13.S127.Mod Certificates.Data.S1277Struct Certificates.Data.S1277Sig
  Certificates.Data.S1277Bfs Std

@[expose] def commN (T : KTab) (x y : Nat) : Nat := mulN T (mulN T (mulN T x y) (invN T x)) (invN T y)


@[expose] def isInvB (B : B6) : Bool := B.comp B == B6.id && B != B6.id

@[expose] def fixCode (B : B6) : List Nat := (List.range 64).filter fun c => B.app c == c

@[expose] def fixInterL (B₁ B₂ : B6) : List Nat :=
  (List.range 64).filter fun c => B₁.app c == c && B₂.app c == c


end Certificates.Data.S1277Cand

end
