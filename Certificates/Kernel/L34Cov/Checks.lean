module

public import Certificates.Data.Kernel.L34Cov.Walk
public import CFSG.Certificates.Kernel.Bounds.L34Alt.Data.F4a
public import CFSG.Certificates.Kernel.Bounds.L34Alt.Data.F4b

public section

namespace CertificateChecks.KernelL34Cov

open CFSG.KC CFSG.KC.L34Cov CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34
open CFSG.Certificates.CosetEnumeration

@[expose] noncomputable def cvId (w : List (Fin 2 × Bool)) (c₁ c₂ c₃ : Nat) : Bool :=
  cvIdOK VT CFSG.KD.L34F4a.Tab CFSG.KD.L34F4b.Tab (w.map letterCode) c₁ c₂ c₃

theorem vt_k : vtOK VT = true := by decide +kernel


end CertificateChecks.KernelL34Cov

end
