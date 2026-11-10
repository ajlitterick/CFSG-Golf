module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC3HCheck
import Certificates.Kernel.Sporadic.OddCore.Outer26100F
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Rows
public import CFSG.Walter.JRFacts

public section

namespace Certificates

open CertificateChecks

theorem certificate26100 : CFSG.EvenSporadicStandard.Fin76b.TC3H.j2OuterOK = true ∧
    CFSG.EvenSporadicStandard.Fin76b.TC3H.j2CountOuter = 0 :=
  ⟨KernelSpor.O26100.outerOK, KernelSpor.O26100.countOuter⟩

end Certificates
