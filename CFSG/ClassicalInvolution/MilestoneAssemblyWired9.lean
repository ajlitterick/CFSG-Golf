module

public import CFSG.ClassicalInvolution.Asc77.SU4ThreeStmt
public import CFSG.ClassicalInvolution.Asc77.WP2Branch
public import CFSG.ClassicalInvolution.Asc77.WP3Fuzzy
public import Mathlib
public import CFSG.ClassicalInvolution.Balance.StrongPowDiagDefs
public import CFSG.ClassicalInvolution.Balance.StrongPowDiagGlue
public import CFSG.ClassicalInvolution.Balance.BootNoTripleDStage
public import CFSG.ClassicalInvolution.Balance.Q27D4Balance
import CFSG.ClassicalInvolution.ModelFacts.ClauseZero
public import CFSG.ClassicalInvolution.SmallCases.DSplitBridge
public import CFSG.ClassicalInvolution.Balance.StrongPowDiagUnitary
public import CFSG.ClassicalInvolution.Balance.StrongLocalBalanceLinearBlocks
public import CFSG.ClassicalInvolution.Balance.LayerGenerationTransport
public import CFSG.Assembly.Subnormal
public import CFSG.Foundations.QuasisimpleMulEquiv
public import CFSG.ClassicalInvolution.Balance.StrongPowDiagMain
public import CFSG.ClassicalInvolution.Balance.StrongPowOrthAniso
public import CFSG.ClassicalInvolution.Balance.StrongPowOrthDelta
public import CFSG.LieType.Universal.SpinOmega.Range
public import CFSG.LieType.Universal.SpinClause0
public import CFSG.ClassicalInvolution.Balance.StrongLocalBalanceSpMain
public import CFSG.ClassicalInvolution.Balance.LayerGenerationPairFinalAll
public import CFSG.ClassicalInvolution.Balance.Q27D4Parts
public import CFSG.ClassicalInvolution.Balance.Q27Layers
public import CFSG.ClassicalInvolution.Balance.QNineFuzzyFree
public import CFSG.ClassicalInvolution.Generic.TypeCSetup2Assembly
public import CFSG.ClassicalInvolution.MilestoneAssemblyWired7
public import CFSG.ClassicalInvolution.MilestoneSU6Piece
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalAll
public import CFSG.ClassicalInvolution.ModelFacts.CommutingFundamentalTwAll
public import CFSG.ClassicalInvolution.ModelFacts.E7ModelFrame
public import CFSG.ClassicalInvolution.ModelFacts.E7ModelPair
public import CFSG.ClassicalInvolution.ModelFacts.E7ModelSignPerp
public import CFSG.ClassicalInvolution.ModelFacts.E7ModelTorus
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2IsogenyAll
public import CFSG.ClassicalInvolution.RouteD.GapsFrBSmallFinal
public import CFSG.ClassicalInvolution.RouteD.GapsFrMinusSmallFinal
public import CFSG.ClassicalInvolution.RouteD.TriageD4
public import CFSG.ClassicalInvolution.RouteD.TriageP1Rows
public import CFSG.ClassicalInvolution.RouteD.TriageSU4Main
public import CFSG.ClassicalInvolution.RouteD.TriageSU4Rigid
public import CFSG.ClassicalInvolution.RouteD.TriageSL4Root
public import CFSG.ClassicalInvolution.RouteD.G2D4A2Classical
public import CFSG.ClassicalInvolution.SmallCases.ConnectedA2FactsMain
public import CFSG.ClassicalInvolution.RouteD.TwinSmallMinusSix
public import CFSG.ClassicalInvolution.RouteD.G2D4Ih8G2
public import CFSG.ClassicalInvolution.Asc77.AscT3TypedExactMain
public import CFSG.ClassicalInvolution.Asc77.AscIH8Rest
public import CFSG.ClassicalInvolution.RouteD.G2D4T3Free
public import CFSG.ClassicalInvolution.RouteD.G2D4Ih8Free
public import CFSG.ClassicalInvolution.SmallCases.NobqLyOut
public import CFSG.ClassicalInvolution.RouteD.TypeE8ExclProved
public import CFSG.ClassicalInvolution.RouteD.TypeE8PartnerWired
public import CFSG.Milestones.CL_LIT_Goldschmidt_strongly_closed_abelian
public import CFSG.ClassicalInvolution.Asc77.AscT3TypedMain
public import CFSG.ClassicalInvolution.Balance.StrongPowSuMain
public import CFSG.ClassicalInvolution.RouteD.G2D4Ih8

public section

namespace CFSG.ClassicalInvolution.MilestoneAssembly

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution CFSG.ClassicalInvolution.RouteD
open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.CoreAssembly
open CFSG.Open (genFittingFStar IsSubnormal classicalInvolutionWitness
  classicalInvolutionTightlyEmbedded lieOrdersChar M11 classicalInvolutionM12)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

variable {p f : ℕ} [Fact p.Prime]

local notation "𝒞" => Generic.CoreAssembly.conjClass

theorem ihAllD_of_minimal {n : ℕ} (hn : Asc77.CITBelowAll p n) (hbig : ¬ CITBelowU p f (n + 1)) :
    Asc77.IHAllD p f := by
  intro G _ _ _ K z h e he
  by_cases hle : Nat.card G ≤ n
  · exact CITBelowU.mono p e hle (hn e he)
  · exact absurd (CITBelowU.mono p f (by omega) h.below) hbig

theorem citBelowAll_of_core (hp2 : p ≠ 2)
    (hcore : ∀ (n f : ℕ), 5 ≤ p ^ f → Asc77.CITBelowAll p n → ¬ CITBelowU p f (n + 1) →
      CoreStep p f)
    (hfund : ∀ f : ℕ, ClassicalIsFundamental p f) (hlift : CentralLift p) (n : ℕ) :
    Asc77.CITBelowAll p n := by
  induction n with
  | zero => exact fun e _ Y _ _ hY => absurd hY (Nat.not_lt_zero _)
  | succ n ih =>
    intro f hq
    by_contra hbig
    have hstep := citStepU_of_coreStep (hcore n f hq ih hbig) (hfund f) hlift n hp2 hq (ih f hq)
    exact hbig fun Y _ _ hY Λ hΛ => (Nat.lt_succ_iff_lt_or_eq.mp hY).elim
      (fun hlt => ih f hq Y hlt Λ hΛ) fun heq => hstep Y heq Λ hΛ

end CFSG.ClassicalInvolution.MilestoneAssembly
