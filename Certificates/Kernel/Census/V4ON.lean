module

public import Certificates.Data.Kernel.OpsV4
public import Certificates.Data.RankThree46Odd.ON
public import Certificates.Kernel.TcGen.ON

set_option maxRecDepth 400000

public section

namespace CFSG.KD.V4ON

open CFSG.KC.OpsV4 CFSG.RankThree.PartTwo.Census CFSG.SectionRank.Native
open CertificateChecks.KernelTc.ON (lay A B)

theorem on_K : v4L lay A B onV4.base onV4.inv₁ onV4.inv₂ = true := by decide +kernel

@[expose] noncomputable def pre (xs : List Nat) (t₁ t₂ : Nat) : Bool :=
  v4L lay A B { onV4.base with nregs := 42, prog := onV4Prog0.take 40, outs := xs } t₁ t₂


end CFSG.KD.V4ON

end
