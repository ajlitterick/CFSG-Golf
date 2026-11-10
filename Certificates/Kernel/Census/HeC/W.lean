module

public import Certificates.Kernel.Census.HeC.K
import all Certificates.Kernel.Census.HeC.Data
import all Certificates.Kernel.Census.HeC.K
import all Certificates.Data.Kernel.Census.HeConj2
import all Certificates.Data.Kernel.Census.PackedConj
import all Certificates.Data.Kernel.Census.Packed
import all CFSG.Certificates.Kernel.Enum.Defs
import all Mathlib.Data.List.Sort
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelCensus.HeCj

open CFSG.KC.HeConj

set_option maxRecDepth 1000000

@[expose] noncomputable def witF (is : List Nat) : Bool :=
  wits8330OK nv CertificateChecks.KernelSporSch.HeTc.nfp uP bsH d is


end CertificateChecks.KernelCensus.HeCj

end
