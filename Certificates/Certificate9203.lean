module

public import CFSG.Sporadic.Co2
public import CFSG.Sporadic.Bridge.TwoGen
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import Certificates.Kernel.Sporadic.Co2.Rels

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Bridge in
open CFSG.Sporadic.SmallF2 CFSG.Sporadic.Th CFSG.Sporadic.Bridge.TwoGen
  CFSG.Sporadic.Bridge.TwoGen.Native TauCeti in
open CFSG.Sporadic.Co2.Native (co2Data) in
theorem certificate9203 : ∀ v ∈ Sporadic.co2Presentation.relatorLetters,
    wordProd (img2 (a co2Data) (b co2Data)) v = 1 := KernelSpor.Co2Rels.relators

end Certificates
