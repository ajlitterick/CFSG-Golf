
module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.HNElevenInputs
import Certificates.Kernel.SporSch.HN.C13607
meta import CFSG.Sporadic.HNSchreier.OrbitCheck
meta import Certificates.Data.CFSGNative.ONSchreier.Vectors
meta import CFSG.Sporadic.HNSchreier.PrimCheck
meta import CFSG.Sporadic.HNSchreier.LocalData
meta import CFSG.Sporadic.HNSchreier.MaskCheck
meta import Certificates.Data.CFSGNative.Perm.Chain

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.HNSchreier.Native CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Native in
theorem certificate13607 : elevenChecksO (hnsData.orbit ()) = true ∧ elevenNatCheck () = true :=
  ⟨KernelSporSch.HN13607.eleven_ok, KernelSporSch.HN13607.nat_ok⟩

end Certificates
