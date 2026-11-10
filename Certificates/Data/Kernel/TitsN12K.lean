module

public import Certificates.Data.Kernel.SporSch.TitsCnt
public import Certificates.Data.Kernel.TitsOctK

public section

namespace CFSG.KC.TitsN12K

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch

@[expose] noncomputable def in2 (a b x : Nat) : Bool := bIf(Nat.beq x a, true, Nat.beq x b)

@[expose] noncomputable def sqB (BP : Nat) (g : Nat → Nat) : Bool :=
  allN 5 (fun t => strictB (pg 11 (mask 11) BP t) (fun b => Nat.beq (g (g b)) b))


@[expose] noncomputable def restK (BP a b : Nat) (g : Nat → Nat) : Bool :=
  bAnd(in2 1 2 (g a), bAnd(in2 1 2 (g b), bAnd(in2 a b (g 2), bAnd(Nat.beq (g 0) 0,
    sqB BP g))))

@[expose] noncomputable def swT (BP : Nat) (g : Nat → Nat) : Bool :=
  strictB (g 1) (fun y => bIf(in2 3 4 y, restK BP 3 4 g, bIf(in2 5 7 y, restK BP 5 7 g,
    bIf(in2 9 13 y, restK BP 9 13 g, bIf(in2 17 25 y, restK BP 17 25 g, false)))))

@[expose] noncomputable def n2T (BP : Nat) (g : Nat → Nat) : Bool :=
  strictB (g 0) (fun y => bAnd(in2 1 2 y, bAnd(Nat.beq (g y) 0, sqB BP g)))


end CFSG.KC.TitsN12K

end
