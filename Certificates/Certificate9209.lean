module

public import CFSG.Sporadic.HS
public import CFSG.Sporadic.Presentation.HSExact
public import CFSG.Sporadic.Bridge.TwoGen
import Certificates.Kernel.Sporadic.HS.Rels
public import CFSG.Sporadic.Presentation.Common

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Bridge in
open CFSG.Sporadic.SmallF2 CFSG.Sporadic.Th CFSG.Sporadic.Bridge.TwoGen
  CFSG.Sporadic.Bridge.TwoGen.Native TauCeti in
open CFSG.Sporadic.HS.Native (hsData) in
theorem certificate9209 : ∀ v ∈ Sporadic.hsPresentation.relatorLetters,
    wordProd (img2 (a hsData) (b hsData)) v = 1 := KernelSpor.HSRels.relators

end Certificates
