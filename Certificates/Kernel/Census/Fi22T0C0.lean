module

public import Certificates.Kernel.Census.Fi22RDefsT0
public import CFSG.Certificates.Kernel.Census.RootConjSound
import Init.Data.Nat.Fold
import Init.Data.Range.Basic
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Foundations.Basic
public import CFSG.LocalAnalysis.ComponentClassification.AS76bDefs
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.GeneralizedFitting
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCo2Pair
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCo2Roots
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock

public section

namespace CertificateChecks.KernelCensus.Fi22K.T0

set_option maxRecDepth 1000000

open CFSG.KC.Census CFSG.ComponentClassification.RankTwoSporadic.Fi22 CertificateChecks.KernelCensus.Fi22K

theorem kC : canonR 3510 12 fi22T0Root = true := by
  quickRfl

end CertificateChecks.KernelCensus.Fi22K.T0

end
