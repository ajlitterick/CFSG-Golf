module

public import CFSG.Certificates.Kernel.Th.Words

public section

namespace CFSG.KC.Th

@[expose] noncomputable def mulB (c rm A B : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun k acc => mstep c rm A B acc k (Nat.mul k (nat_lit 256))) (nat_lit 248)


@[expose] noncomputable def vecB (rm v M : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun k acc => Nat.xor acc (Nat.mul (Nat.land (Nat.shiftRight v k) (nat_lit 1))
      (Nat.land (Nat.shiftRight M (Nat.mul k (nat_lit 256))) rm))) (nat_lit 248)


@[expose] noncomputable def trLvl (s m x : Nat) : Nat :=
  (fun t => Nat.xor x (Nat.lor t (Nat.shiftLeft t (Nat.mul (nat_lit 255) s))))
    (Nat.land (Nat.xor x (Nat.shiftRight x (Nat.mul (nat_lit 255) s))) m)

@[expose] noncomputable def trB (m0 m1 m2 m3 m4 m5 m6 m7 x : Nat) : Nat :=
  trLvl (nat_lit 1) m0 (trLvl (nat_lit 2) m1 (trLvl (nat_lit 4) m2 (trLvl (nat_lit 8) m3
    (trLvl (nat_lit 16) m4 (trLvl (nat_lit 32) m5 (trLvl (nat_lit 64) m6 (trLvl (nat_lit 128) m7 x)))))))


@[expose] noncomputable def chkUni (up dg M : Nat) : Bool :=
  andB (Nat.beq (Nat.land M up) (nat_lit 0)) (Nat.beq (Nat.land M dg) dg)

@[expose] noncomputable def chkNe (a b : Nat) : Bool := Bool.rec true false (Nat.beq a b)

@[expose] noncomputable def inW (x w1 w2 : Nat) : Bool :=
  orB (Nat.beq x w1) (orB (Nat.beq x w2) (Nat.beq x (Nat.xor w1 w2)))

@[expose] noncomputable def chkInW (rm v g w1 w2 : Nat) : Bool := inW (vecB rm v g) w1 w2

@[expose] noncomputable def cmin (a b : Nat) : Nat := Bool.rec b a (Nat.blt a b)
@[expose] noncomputable def cmax (a b : Nat) : Nat := Bool.rec a b (Nat.blt a b)

@[expose] noncomputable def canon3 (a b c : Nat) : Nat :=
  Nat.lor (cmin a (cmin b c)) (Nat.shiftLeft (cmax (cmin a b) (cmin (cmax a b) c)) (nat_lit 256))

@[expose] noncomputable def canon2 (u v : Nat) : Nat := canon3 u v (Nat.xor u v)

@[expose] noncomputable def planeStep (rm g P : Nat) : Nat :=
  canon2 (vecB rm (Nat.land P rm) g) (vecB rm (Nat.shiftRight P (nat_lit 256)) g)

@[expose] noncomputable def bit (x i : Nat) : Nat := Nat.land (Nat.shiftRight x i) (nat_lit 1)

@[expose] noncomputable def rowB (rm G r : Nat) : Nat := Nat.land (Nat.shiftRight G (Nat.mul r (nat_lit 256))) rm

@[expose] noncomputable def blk (r0 r1 j : Nat) : Nat :=
  Nat.add (Nat.add (bit r0 (Nat.mul (nat_lit 2) j)) (Nat.mul (nat_lit 2) (bit r0 (Nat.succ (Nat.mul (nat_lit 2) j)))))
    (Nat.add (Nat.mul (nat_lit 4) (bit r1 (Nat.mul (nat_lit 2) j))) (Nat.mul (nat_lit 8) (bit r1 (Nat.succ (Nat.mul (nat_lit 2) j)))))

@[expose] noncomputable def det2 (a : Nat) : Nat :=
  Nat.xor (Nat.mul (bit a (nat_lit 0)) (bit a (nat_lit 3))) (Nat.mul (bit a (nat_lit 1)) (bit a (nat_lit 2)))

@[expose] noncomputable def mul2 (a b : Nat) : Nat :=
  Nat.add (Nat.add (Nat.xor (Nat.mul (bit a (nat_lit 0)) (bit b (nat_lit 0))) (Nat.mul (bit a (nat_lit 1)) (bit b (nat_lit 2))))
      (Nat.mul (nat_lit 2) (Nat.xor (Nat.mul (bit a (nat_lit 0)) (bit b (nat_lit 1))) (Nat.mul (bit a (nat_lit 1)) (bit b (nat_lit 3))))))
    (Nat.add (Nat.mul (nat_lit 4) (Nat.xor (Nat.mul (bit a (nat_lit 2)) (bit b (nat_lit 0))) (Nat.mul (bit a (nat_lit 3)) (bit b (nat_lit 2)))))
      (Nat.mul (nat_lit 8) (Nat.xor (Nat.mul (bit a (nat_lit 2)) (bit b (nat_lit 1))) (Nat.mul (bit a (nat_lit 3)) (bit b (nat_lit 3))))))

@[expose] noncomputable def t2 (a : Nat) : Nat :=
  Nat.lor (Nat.lor (Nat.land a (nat_lit 9)) (Nat.shiftLeft (Nat.land a (nat_lit 2)) (nat_lit 1)))
    (Nat.shiftRight (Nat.land a (nat_lit 4)) (nat_lit 1))


@[expose] noncomputable def blkG (rm G i j : Nat) : Nat :=
  blk (rowB rm G (Nat.mul (nat_lit 2) i)) (rowB rm G (Nat.succ (Nat.mul (nat_lit 2) i))) j


@[expose] noncomputable def lcmN (a b : Nat) : Nat := Nat.div (Nat.mul a b) (Nat.gcd a b)

@[expose] noncomputable def fld32 (x k : Nat) : Nat := Nat.land (Nat.shiftRight x (Nat.mul (nat_lit 32) k)) (nat_lit 4294967295)

@[expose] noncomputable def subsetSize (sizes mask n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 1)
    (fun k acc => Nat.add acc (Nat.mul (bit mask k) (fld32 sizes k))) n

@[expose] noncomputable def primOK (sizes n N : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun mask acc => andB acc (orB (orB (Nat.beq mask (nat_lit 0))
        (Nat.beq mask (Nat.sub (Nat.shiftLeft (nat_lit 1) n) (nat_lit 1))))
      (Bool.rec true false (Nat.beq (Nat.mod N (subsetSize sizes mask n)) (nat_lit 0)))))
    (Nat.shiftLeft (nat_lit 1) n)

end CFSG.KC.Th

end
