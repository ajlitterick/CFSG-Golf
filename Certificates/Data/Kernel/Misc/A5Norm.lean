module

public import Certificates.Data.Kernel.Misc.Sp4Cen

public section

namespace CFSG.KD.A5Norm

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc.GL4


@[expose] noncomputable def incF (l : List Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun a _ ih p => andB (Nat.blt p a) (ih a)) l

@[expose] noncomputable def incL (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun a l _ => incF l a) l


end CFSG.KD.A5Norm

end
