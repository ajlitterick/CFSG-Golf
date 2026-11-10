module

public import CFSG.Certificates.Kernel.LieCocycle.Fi22.Core

public section

namespace CFSG.KLC.Fi22

open CFSG.KC.Loop


@[expose] noncomputable def commOk (A B n : Nat) : Bool :=
  fsplit (nat_lit 1024) (nat_lit 6) A (fun FA => fsplit (nat_lit 1024) (nat_lit 6) B (fun FB =>
    allLt n (fun i => Nat.beq (ent FA (ent FB i)) (ent FB (ent FA i)))))


end CFSG.KLC.Fi22

end
