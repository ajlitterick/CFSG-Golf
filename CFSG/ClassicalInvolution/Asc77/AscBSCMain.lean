module

public import CFSG.ClassicalInvolution.Asc77.AscBSCResid
public import CFSG.ClassicalInvolution.Asc77.AscBSCShape
import CFSG.ClassicalInvolution.Asc77.WP3S28BIndep
import CFSG.ClassicalInvolution.ModelFacts.CommutingFundamentalTwAll
import CFSG.ClassicalInvolution.Balance.LayerGenerationPairFinalAll

public section

namespace CFSG.ClassicalInvolution.Asc77.BSC

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Disconnected
open CFSG.Assembly.LowTwoRank

set_option linter.unusedSectionVars false

variable {p f : ℕ} [Fact p.Prime]


theorem noFuzzyFrame {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {K : Subgroup G} {z : G}
    (hS : BootSetting p f K z) :
    ∀ A : Subgroup G, ¬ Theorem5.FuzzyFrameOn p f (CoreAssembly.conjClass K) A := by
  intro A hA
  have hΩ := NDB.Cover.hypOmegaMod hS.nonabelian hS.odd hS.five hS.member hS.below
  exact hS.noTriple (S28B.indepTriple_of_fuzzy (Balance.Bootstrap.layerGenerationHybrid p)
    (ModelFacts.commutingFundamentalFactsFive_all hS.odd) hS.nonabelian hS.odd hS.five hS.member
    hΩ hS.below hS.dconn ⟨A, hA⟩)


end CFSG.ClassicalInvolution.Asc77.BSC
