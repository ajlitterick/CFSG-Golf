module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.SimsSporJ4Data
import Certificates.Kernel.J4Row.Duad
public import CFSG.Sporadic.J4.QTNative
public import CFSG.Sporadic.Schreier.J4SNative
public import CFSG.Sporadic.Schreier.M24Data
public import Certificates.Data.CFSGNative.SporadicSchreier.MathieuOddCore

public section

namespace Certificates

open CertificateChecks

open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.SimsSporJ4 in
theorem certificate40362 : Nat.card {σ : CFSG.Blueprint.NativeSporadic.M24 //
      (σ : Equiv.Perm (Fin 24)) * row31.piPerm = row31.piPerm * σ ∧
        (σ : Equiv.Perm (Fin 24)) * duadSwap = duadSwap * σ} = 10 ∧
    Nat.card {σ : CFSG.Blueprint.NativeSporadic.M24 //
      (σ : Equiv.Perm (Fin 24)) * row43.piPerm = row43.piPerm * σ ∧
        (σ : Equiv.Perm (Fin 24)) * duadSwap = duadSwap * σ} = 14 :=
  ⟨KernelJ4Row.card_duad31, KernelJ4Row.card_duad43⟩

end Certificates
