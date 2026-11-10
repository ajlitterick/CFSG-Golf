module

public import CFSG.Certificates.Kernel.Enum.Defs
public import Certificates.Data.Kernel.DecText
public import Certificates.Data.Kernel.EvenSporM22.M22StdDefs

public section

namespace CFSG.KC.I22F

open CFSG.KC.Enum CFSG.KC.LQT.Cov CFSG.KC.LQT.Syl CFSG.KC.M22S


@[expose] noncomputable def lsel (A AI B BI : Nat) (l : Nat × Bool) : Nat :=
  Prod.rec (motive := fun _ => Nat) (fun g s => nIf(Nat.beq g (nat_lit 0),
    Bool.rec (motive := fun _ => Nat) AI A s, Bool.rec (motive := fun _ => Nat) BI B s)) l

@[expose] noncomputable def wimg (A AI B BI : Nat) (v : List (Nat × Bool)) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun p => p)
    (fun l _ ih p => pg (nat_lit 15) (nat_lit 32767) (lsel A AI B BI l) (ih p)) v


@[expose] def lB : Nat × Bool := (1, true)


end CFSG.KC.I22F

end
