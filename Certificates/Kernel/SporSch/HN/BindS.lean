module

public import Certificates.Data.Kernel.SporSch.HNXBind
public import CFSG.Sporadic.HNSchreier.EmbeddedOrbit

public section

namespace CertificateChecks.KernelSporSch.HNXBind

open CFSG.KS.SporSch CFSG.Sporadic.HNSchreier.Native

theorem bindS : hnxShapeK (hnsOrbitData ()) = true := by decide +kernel


end CertificateChecks.KernelSporSch.HNXBind

end
