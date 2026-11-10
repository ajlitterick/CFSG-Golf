module

public import CFSG.Certificates.Kernel.Orders.Mat
public import CFSG.Certificates.Kernel.Orders.HN.Data.Const
public import CFSG.Certificates.Kernel.Local.LargeCore.Grp

public section

namespace CFSG.KC.LL.HN

open CFSG.KC.Loop CFSG.KC.LL

@[expose] noncomputable def mm (a b : Nat) : Nat :=
  CFSG.KC.Ord.mulR (nat_lit 5) (nat_lit 13) (nat_lit 1729) (nat_lit 133) (nat_lit 9)
    CFSG.KD.OrdHN.L CFSG.KD.OrdHN.H CFSG.KD.OrdHN.CM CFSG.KD.OrdHN.RM a b

@[expose] noncomputable def ln (v j : Nat) : Nat := fldW v (Nat.mul (nat_lit 13) j) (nat_lit 13)

@[expose] noncomputable def rev (v : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun j acc => Nat.lor acc (Nat.shiftLeft (ln v j) (Nat.mul (nat_lit 13) (Nat.sub (nat_lit 132) j)))) (nat_lit 133)

@[expose] noncomputable def cvR (a r : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Nat.lor acc (Nat.shiftLeft
      (Nat.mod (fldW (Nat.mul (fldW a (Nat.mul (nat_lit 1729) i) (nat_lit 1729)) r) (nat_lit 1716) (nat_lit 13)) (nat_lit 5))
      (Nat.mul (nat_lit 13) i))) (nat_lit 133)

@[expose] noncomputable def cv (a v : Nat) : Nat := cvR a (rev v)


@[expose] noncomputable def subI (M : Nat) : Nat :=
  CFSG.KC.Ord.redP (nat_lit 13) CFSG.KD.OrdHN.L CFSG.KD.OrdHN.H (nat_lit 5) (nat_lit 9)
    (Nat.add M (Nat.mul CFSG.KD.OrdHN.ONE (nat_lit 4)))

@[expose] noncomputable def fixAll (M : Nat) (vs : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun v _ ih => bAnd(Nat.beq (cv M v) v, ih)) vs


@[expose] noncomputable def ord3 (x : Nat) : Bool :=
  bAnd(Nat.beq (mm x (mm x x)) CFSG.KD.OrdHN.ONE, bIf(Nat.beq x CFSG.KD.OrdHN.ONE, false, true))


end CFSG.KC.LL.HN

end
