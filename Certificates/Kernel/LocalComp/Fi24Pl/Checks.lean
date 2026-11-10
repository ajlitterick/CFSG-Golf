module

public import Certificates.Kernel.LocalComp.Fi24Pl.Data
public import Certificates.Kernel.LocalComp.Fi24TwoB.E15027
public import Certificates.Data.Kernel.Fi24Pl.Defs
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.Fi24PlK

open CFSG.KC.Enum CFSG.KC.Fi24Pl CertificateChecks.KernelLC

@[expose] noncomputable def iotaC (c : Nat) : Bool :=
  allN (nat_lit 16) fun l => strictB (Nat.add (Nat.mul (nat_lit 16) c) l) fun i =>
    bIf(Nat.blt i (nat_lit 243), iotaK Fi24PlT.A.F Fi24PlD.IK i, true)

@[expose] noncomputable def row (c : Nat) : Bool := rowC Fi24PlD.IK Fi24PlD.V Fi24BN.T Fi24PlD.BT c

theorem basis : basisK Fi24PlT.A.F = true := by quickRfl

theorem inv : invK Fi24PlD.IK Fi24PlD.V = true := by quickRfl

theorem norm : normK Fi24PlT.A.F Fi24BN.G Fi24BN.T Fi24PlD.MK = true := by quickRfl

theorem final : finalK Fi24PlD.BT = true := by quickRfl


end CertificateChecks.KernelLC.Fi24PlK

#kc_each CertificateChecks.KernelLC.Fi24PlK.iotaC 0 16
#kc_each CertificateChecks.KernelLC.Fi24PlK.row 0 64

end
