
module

public meta import CFSG.Sporadic.Co2Schreier.Arrays
public meta import Certificates.Data.CFSGNative.Schreier.Check
public meta import CFSG.Sporadic.Co2Schreier.ChainCheck
public meta import Std.Data.HashMap
public meta import CFSG.Sporadic.Co2Schreier.OrbitCheck
public meta import CFSG.Sporadic.Co2Schreier.WitCheck
public meta import CFSG.Sporadic.Co2Schreier.Lin
public meta import CFSG.Sporadic.Co2Schreier.Text
public import Certificates.Kernel.Co2I301.CentProof
public import Certificates.Kernel.Co2I301.SmallProof

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Co2I301 in
theorem certificate810301 : smallCheck () = true ∧
    (
      RowCentFacts) ∧
    (RowSixFacts) :=
  ⟨KernelCo2I301.small_check, by
    intros
    have : Fact (CFSG.Sporadic.Co2I301.smallCheck () = true) := ⟨KernelCo2I301.small_check⟩
    exact KernelCo2I301.cent_facts, KernelCo2I301.six_facts⟩

end Certificates
