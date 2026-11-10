module

public import Certificates.Data.Kernel.J4Loc.Trio
public import Certificates.Kernel.J4Loc.TrioData
public import Certificates.Kernel.J4Q.MaskData
public import Certificates.Kernel.J4Q.MaskBlkData
public import Certificates.Kernel.J4Q.AllN
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Loc

open CFSG.KC.J4Q CFSG.KC.J4Loc CFSG.KD.J4Loc CFSG.KD.J4Q

@[expose] noncomputable def ch4174S (b : Nat) : Bool := subOK SB SBK mkKT mkKIT b

#j4q_all CFSG.KD.J4Loc.SUB CertificateChecks.KernelJ4Loc.ch4174S 22

@[expose] noncomputable def ch4174C (b : Nat) : Bool := chainOK SB SBK mkKT (nat_lit 22) b

#j4q_all CFSG.KD.J4Loc.CHN CertificateChecks.KernelJ4Loc.ch4174C 22

theorem ch4174_inv : invOK mkTLB INVS = true := by quickRfl

@[expose] noncomputable def ch4174X (b : Nat) : Bool :=
  xOK SB SBK mkTLB INVS TRK (nat_lit 3795) TRI0 b

#j4q_all CFSG.KD.J4Loc.XC CertificateChecks.KernelJ4Loc.ch4174X 22

@[expose] noncomputable def ch4174A (b : Nat) : Bool := aboveOK SB SBK TRK (nat_lit 3795) TRI0 b

#j4q_all CFSG.KD.J4Loc.AB CertificateChecks.KernelJ4Loc.ch4174A 22


end CertificateChecks.KernelJ4Loc

end
