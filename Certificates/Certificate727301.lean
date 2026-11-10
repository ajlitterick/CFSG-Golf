
module

public import CFSG.Sporadic.SuzRecog.SuzL34.Facts
meta import CFSG.Sporadic.SuzOddCore.ArraysCheck
meta import Certificates.Data.CFSGNative.Schreier.Refine
meta import Certificates.Data.CFSGNative.Perm.Chain
meta import CFSG.Sporadic.SuzOddCore.InvArrays
meta import CFSG.Sporadic.SuzOddCore.InvArraysCheck
meta import Certificates.Data.CFSGNative.Schreier.Check
meta import Mathlib.Data.Fintype.Card
meta import CFSG.Sporadic.SuzOddCore.InvGraphCheck
meta import CFSG.Sporadic.SuzOddCore.SmallChainCheck
import Certificates.Kernel.Sporadic.OddCore.SuzBtCG
import Certificates.Kernel.Sporadic.OddCore.SuzBtLG
import Certificates.Kernel.Sporadic.OddCore.SuzBtVG
import Certificates.Kernel.Sporadic.OddCore.SuzBtQG
import Certificates.Kernel.Sporadic.OddCore.SuzBtWG

public section

namespace Certificates

open CertificateChecks.KernelSpor

open CFSG in
theorem certificate727301 : CFSG.Sporadic.SuzRecog.SuzL34Cert.F1Prop ∧
    CFSG.Sporadic.SuzRecog.SuzL34Cert.F1MProp ∧
    CFSG.Sporadic.SuzRecog.SuzL34Cert.F2Prop ∧
    CFSG.Sporadic.SuzRecog.SuzL34Cert.F3Prop ∧
    CFSG.Sporadic.SuzRecog.SuzL34Cert.F4Prop ∧
    CFSG.Sporadic.SuzRecog.SuzL34Cert.F5Prop ∧
    CFSG.Sporadic.SuzRecog.SuzL34Cert.F6Prop ∧
    CFSG.Sporadic.SuzRecog.SuzL34Cert.F7Prop ∧
    CFSG.Sporadic.SuzRecog.SuzL34Cert.F8Prop :=
  ⟨SuzBtCG.f1Prop, SuzBtZG.f1mProp, SuzBtLG.f2Prop, SuzBtOG.f3Prop, SuzBtTG.f4Prop,
    SuzBtFG.f5Prop, SuzBtVG.f6Prop, SuzBtQG.f7Prop, SuzBtWG.f8Prop⟩

end Certificates
