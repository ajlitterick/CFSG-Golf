module

public import Certificates.Kernel.Sporadic.ON.Data
public import Certificates.Kernel.Sporadic.FLGen
public import CFSG.Certificates.Kernel.Spor.TabWords
import Certificates.Kernel.Sporadic.OrbRecGen
public meta import Certificates.Kernel.Sporadic.ON.Data
public meta import CFSG.Sporadic.Schreier.ONActionData
public meta import Lean

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ON

meta def bigT (h : Nat) (u : Bool) : Array Nat :=
  let t := strongM[h]!
  CFSG.KS.ONGen.leaves 18 9 (if u then CFSG.KS.RawGen.inv t.size t else t)

meta def bT0 : Array Nat := bigT 0 false
meta def bT1 : Array Nat := bigT 1 false
meta def bT2 : Array Nat := bigT 2 false
meta def bT3 : Array Nat := bigT 3 false
meta def bT4 : Array Nat := bigT 4 false
meta def bT5 : Array Nat := bigT 5 false
meta def bT6 : Array Nat := bigT 6 false
meta def bU0 : Array Nat := bigT 0 true
meta def bU1 : Array Nat := bigT 1 true
meta def bU2 : Array Nat := bigT 2 true
meta def bU3 : Array Nat := bigT 3 true
meta def bU4 : Array Nat := bigT 4 true
meta def bU5 : Array Nat := bigT 5 true
meta def bU6 : Array Nat := bigT 6 true

end CertificateChecks.KernelSpor.ON

#kc_nattree CertificateChecks.KernelSpor.ONB.A CertificateChecks.KernelSpor.ON.bT0
#kc_nattree CertificateChecks.KernelSpor.ONB.U0 CertificateChecks.KernelSpor.ON.bU0
#kc_nattree CertificateChecks.KernelSpor.ONB.B CertificateChecks.KernelSpor.ON.bT1
#kc_nattree CertificateChecks.KernelSpor.ONB.U1 CertificateChecks.KernelSpor.ON.bU1
#kc_nattree CertificateChecks.KernelSpor.ONB.T2 CertificateChecks.KernelSpor.ON.bT2
#kc_nattree CertificateChecks.KernelSpor.ONB.U2 CertificateChecks.KernelSpor.ON.bU2
#kc_nattree CertificateChecks.KernelSpor.ONB.T3 CertificateChecks.KernelSpor.ON.bT3
#kc_nattree CertificateChecks.KernelSpor.ONB.U3 CertificateChecks.KernelSpor.ON.bU3
#kc_nattree CertificateChecks.KernelSpor.ONB.T4 CertificateChecks.KernelSpor.ON.bT4
#kc_nattree CertificateChecks.KernelSpor.ONB.U4 CertificateChecks.KernelSpor.ON.bU4
#kc_nattree CertificateChecks.KernelSpor.ONB.T5 CertificateChecks.KernelSpor.ON.bT5
#kc_nattree CertificateChecks.KernelSpor.ONB.U5 CertificateChecks.KernelSpor.ON.bU5
#kc_nattree CertificateChecks.KernelSpor.ONB.T6 CertificateChecks.KernelSpor.ON.bT6
#kc_nattree CertificateChecks.KernelSpor.ONB.U6 CertificateChecks.KernelSpor.ON.bU6

namespace CertificateChecks.KernelSpor.ON

open CFSG.KC.Enum CFSG.KS CFSG.KS.ON CFSG.KS.TW CFSG.KS.Words CFSG.KS.FLGen

@[expose] noncomputable def tb (T : Nat → Nat) (i : Nat) : Nat :=
  rget T (nat_lit 9) (nat_lit 511) (nat_lit 18) (mask (nat_lit 18)) i

@[expose] noncomputable def TB (h i : Nat) : Nat :=
  nIf(Nat.beq h 0, tb ONB.A i, nIf(Nat.beq h 1, tb ONB.B i, nIf(Nat.beq h 2, tb ONB.T2 i,
    nIf(Nat.beq h 3, tb ONB.T3 i, nIf(Nat.beq h 4, tb ONB.T4 i, nIf(Nat.beq h 5, tb ONB.T5 i,
      tb ONB.T6 i))))))

@[expose] noncomputable def UB (h i : Nat) : Nat :=
  nIf(Nat.beq h 0, tb ONB.U0 i, nIf(Nat.beq h 1, tb ONB.U1 i, nIf(Nat.beq h 2, tb ONB.U2 i,
    nIf(Nat.beq h 3, tb ONB.U3 i, nIf(Nat.beq h 4, tb ONB.U4 i, nIf(Nat.beq h 5, tb ONB.U5 i,
      tb ONB.U6 i))))))

end CertificateChecks.KernelSpor.ON

#kon_flists CertificateChecks.KernelSpor.ON.tb CertificateChecks.KernelSpor.ONB
  CertificateChecks.KernelSpor.ONB.FL CFSG.ONSchreier.Data.strongWords 2 7

#kon_nests CertificateChecks.KernelSpor.ON.tb CertificateChecks.KernelSpor.ONB
  CertificateChecks.KernelSpor.ONB.NE CFSG.ONSchreier.Data.strongWords 2 7

namespace CertificateChecks.KernelSpor.ON

open CFSG.KC.Enum CFSG.KS CFSG.KS.ON CFSG.KS.TW CFSG.KS.Words CFSG.KS.FLGen

@[expose] noncomputable def FL (j : Nat) : List (Nat → Nat) :=
  cond (Nat.beq j 2) ONB.FL2 (cond (Nat.beq j 3) ONB.FL3 (cond (Nat.beq j 4) ONB.FL4
    (cond (Nat.beq j 5) ONB.FL5 ONB.FL6)))

@[expose] noncomputable def NE (j : Nat) : Nat → Nat :=
  cond (Nat.beq j 2) ONB.NE2 (cond (Nat.beq j 3) ONB.NE3 (cond (Nat.beq j 4) ONB.NE4
    (cond (Nat.beq j 5) ONB.NE5 ONB.NE6)))

@[expose] noncomputable def trAtF (x : Nat) : Bool :=
  bAnd(allBlk (nat_lit 0) (fun h => strictB (TT h x) fun y => bAnd(Nat.blt y (nat_lit 245520),
      bAnd(Nat.blt (UU h x) (nat_lit 245520), Nat.beq (UU h y) x))) (nat_lit 7),
    bAnd(allBlk (nat_lit 0) (fun h => bAnd(Nat.beq (TB h x) (TT h x), Nat.beq (UB h x) (UU h x)))
        (nat_lit 7),
      allBlk (nat_lit 2) (fun j => Nat.beq (TT j x) (NE j x)) (nat_lit 5)))

@[expose] noncomputable def trF (s : Nat) : Bool :=
  allBlk (Nat.mul s (nat_lit 240)) trAtF (nat_lit 240)


theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

section


end


end CertificateChecks.KernelSpor.ON

end
