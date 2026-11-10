
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
import Certificates.Kernel.Sporadic.OddCore.SuzBtBG

public section

namespace Certificates

open CertificateChecks.KernelSpor

open CFSG in
theorem certificate727303 : CFSG.Sporadic.SuzRecog.SuzL34Cert.F6bProp :=
  SuzBtBG.f6bProp

end Certificates
