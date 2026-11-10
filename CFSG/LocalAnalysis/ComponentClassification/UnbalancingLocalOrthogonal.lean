module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalOrthogonalBlocks
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSASymplecticExclusion
public import CFSG.LocalAnalysis.ComponentInitial.CentralSL2Semilinear

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancingLocal

open Matrix CFSG.Assembly.LowTwoRank
open scoped commutatorElement MatrixGroups

namespace OrthogonalExclusion

open OrthogonalBlocks OrthogonalBlocks.HypForm LocalAnalysis.ComponentInitial


section Odd


end Odd

section Two


end Two


end OrthogonalExclusion

open OrthogonalExclusion


end CFSG.ComponentClassification.UnbalancingLocal
