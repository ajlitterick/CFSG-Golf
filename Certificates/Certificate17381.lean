
module

public import Certificates.Kernel.SporSch.HN.C17381
public meta import CFSG.Sporadic.HNSchreier.PrimCheck
public meta import CFSG.Sporadic.HNSchreier.LocalData
public meta import CFSG.Sporadic.HNSchreier.MaskCheck
public meta import CFSG.Sporadic.HNSchreier.LocalCheck
public meta import CFSG.Sporadic.HNSchreier.FAData

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.HNSchreier.Native CFSG.HardMathSupport.Dickson.I271.HNFive.Native in
theorem certificate17381 : hn5CheckO (hnsData.orbit ()) = true :=
  KernelSporSch.HN17381.check17381

end Certificates
