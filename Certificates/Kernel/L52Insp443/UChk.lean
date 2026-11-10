module

public import Certificates.Kernel.L52Insp443.Data
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelL52I

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc.GLM CFSG.KC.L52I

@[expose] noncomputable def unitsK (K : List Nat) (cnt : Nat) : List Nat :=
  Nat.rec (motive := fun _ => List Nat) List.nil
    (fun d acc => Bool.rec (motive := fun _ => List Nat) acc (List.cons (xsel K d) acc)
      (Nat.beq (rankK (xsel K d)) (nat_lit 5))) cnt

@[expose] noncomputable def vChk (L bs zS wS ps qs : List Nat) : Bool :=
  andB (nodupK L) (andB (Nat.beq (List.length L) (nat_lit 128))
    (allK (fun c => andB (unitK' c) (andB (allK (commK c) bs)
      (orB (notB (conjCommK c ps qs)) (orB (memK c zS) (memK c wS))))) L))
where
  unitK' (c : Nat) : Bool := andB (Nat.blt c (nat_lit 33554432)) (Nat.beq (rankK c) (nat_lit 5))

@[expose] noncomputable def ch725109v (k : Nat) : Bool :=
  vChk (unitsK (D.k1K.getD k []) (nat_lit 512)) (D.k1B.getD k [])
    (D.zS.getD (D.k1zw.getD k (0, 0)).1 []) (D.wS.getD (D.k1zw.getD k (0, 0)).2 []) D.x7p D.x7q

@[expose] noncomputable def ch725109i (_ : Nat) : Bool := allK vChk.unitK' D.x7q

#kc_each ch725109v 0 6
#kc_each ch725109i 0 1


end CertificateChecks.KernelL52I

end
