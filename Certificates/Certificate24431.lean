module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.J3Inputs
import Certificates.Kernel.Sporadic.OddCore.J3SylData
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

theorem certificate24431 : (CFSG.EvenSporadicStandard.HypOne.J3.sylowData = true) ∧
    (CFSG.EvenSporadicStandard.HypOne.J3.e8Data = true) ∧
    (CFSG.EvenSporadicStandard.HypOne.J3.foursData = true) :=
  KernelSpor.J3SylData.facts24431

end Certificates
