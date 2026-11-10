module

public import CFSG.Certificates.Kernel.MonsterConv.Perm

public section

namespace CFSG.KC.MonsterConv.Perm

open CFSG.KC

@[expose] noncomputable def dswValid (W d m : Nat) : Bool :=
  andB (Nat.beq (Nat.land m (Nat.shiftLeft m d)) (nat_lit 0))
    (Nat.beq (Nat.shiftRight m (Nat.sub W d)) (nat_lit 0))

@[expose] noncomputable def netValid (k N : Nat) : Bool :=
  (fun W => andB (Nat.blt N (Nat.shiftLeft (nat_lit 1) (Nat.mul (Nat.sub (Nat.mul (nat_lit 2) k) (nat_lit 1)) W)))
      (Nat.rec (motive := fun _ => Bool) true
        (fun i ih => andB ih
          (dswValid W (stageShift k i) (Nat.land (Nat.shiftRight N (Nat.mul i W)) (ones W))))
        (Nat.sub (Nat.mul (nat_lit 2) k) (nat_lit 1))))
    (Nat.shiftLeft (nat_lit 1) k)

@[expose] noncomputable def netsValid (k : Nat) (Ns : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun N _ ih => andB (netValid k N) ih) Ns


@[expose] noncomputable def wordNetV (k : Nat) (Ns : List Nat) (N : Nat) : Bool :=
  andB (andB (netsValid k Ns) (netValid k N)) (wordNet k Ns N)


end CFSG.KC.MonsterConv.Perm

end
