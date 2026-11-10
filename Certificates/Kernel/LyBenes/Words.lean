module

public import Certificates.Kernel.LyBenes.Data
public import CFSG.Sporadic.Recognition.LyonsFinalCore107
public import CFSG.Sporadic.Recognition.LyonsFinalModularInputs
public import CFSG.Sporadic.Recognition.LyonsFinalDist2Inputs

public section

namespace CertificateChecks.KernelLyB

open CFSG.KC.LyBenes CFSG.Sporadic.Recognition.LyonsSims.LyFinal


@[expose] noncomputable def stepsAt (i : Nat) : List Dist2Step :=
  (dist2Derivs.getD i ⟨"", []⟩).steps


end CertificateChecks.KernelLyB

end
