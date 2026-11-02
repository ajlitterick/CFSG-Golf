module

public import CFSG.ClassicalInvolution.MilestoneAssemblyWired
public import CFSG.ClassicalInvolution.Generic.TypeCSmallRecognition
public import CFSG.ClassicalInvolution.Generic.TypeCSmallSetup
public import CFSG.ClassicalInvolution.RouteD.AllA1
public import CFSG.ClassicalInvolution.RouteD.TypeUPatternEnd
public import CFSG.ClassicalInvolution.RouteD.TypeUPatternFive
public import CFSG.ClassicalInvolution.SmallCases.UpgradeRest
public import CFSG.ClassicalInvolution.Balance.BootstrapBootTripleNine
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPreimages
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
public import CFSG.LocalAnalysis.SignalizerFunctor

public section

namespace CFSG.ClassicalInvolution.MilestoneAssembly

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution CFSG.ClassicalInvolution.RouteD
open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.CoreAssembly
open CFSG.Open (genFittingFStar IsSubnormal classicalInvolutionWitness
  classicalInvolutionTightlyEmbedded lieOrdersChar M11 classicalInvolutionM12)

variable {p f : ℕ} [Fact p.Prime]

local notation "𝒞" => Generic.CoreAssembly.conjClass

@[expose] def ShapeSU34 (a : ℕ) (t : StatedLieTag) (n : ℕ) : Prop :=
  a = 1 ∧ t = .PSU ∧ (n = 3 ∨ n = 4)

theorem pieceSUs_of_parts (hMFZ : Gaps.FundNoncentral p) (h34 : RowPiece p f ShapeSU34) :
    PieceSUs p f := by
  intro a t n hshape
  obtain ⟨rfl, rfl, h3, h5⟩ := hshape
  by_cases hn : n = 5
  · subst hn
    intro G _ _ _ hnab K z S hS
    obtain ⟨D, -, -⟩ := routeD_typeU_four hMFZ S.odd S.five S.inClass S.exact
      (mem_conjClass_self K) (single_class K) S.conn S.cls hS.exists_two_components S.p1
    exact ⟨D⟩
  · exact h34 1 .PSU n ⟨rfl, rfl, by omega⟩

theorem pieceSU6_of_phanE6 (hMFZ : Gaps.FundNoncentral p) (hPhan : PhanE6 p f) :
    PieceSU6 p f := by
  intro a t n hshape G _ _ _ hnab K z S hS
  obtain ⟨rfl, rfl, rfl⟩ := hshape
  rcases routeD_typeU_five_final hMFZ S.odd S.five hPhan S.inClass S.exact
    (mem_conjClass_self K) (single_class K) S.conn S.cls hS.exists_two_components S.p1 with
    ⟨D, -, -⟩ | ⟨D, -, -⟩
  · exact ⟨D⟩
  · exact ⟨D⟩

structure CoreOpenWired₃ (p f : ℕ) [Fact p.Prime] : Prop where
  disconnected : SmallDisconnected p f
  connectedA2 : ConnectedA2.ConnectedA2Inputs p f
  typeCSetup : SmallTypeCSetup p f
  psp6 : PSp6Recognition p f
  exc : ModelFacts.ClassicalMembersFundamentalExc2 p f
  params : Upgrade.ClassicalMemberParametersRest p f
  frameMF1 : Balance.Bootstrap.FrameMF1 p f
  frameCoverage : Balance.Bootstrap.FrameCoverage p f
  frameLevi : Balance.Bootstrap.FrameLevi p f
  bootTriple27 : p ^ f = 27 → BootTriple p f
  bootNoTriple : BootNoTriple p f
  sl3 : PieceSL3Big p f
  phanE6 : PhanE6 p f
  su34 : RowPiece p f ShapeSU34
  sp3 : PieceSp3 p f
  e7 : E7PartnerExists p f
  e8 : E8PartnerExists p f
  twinD : TwinDPartnerPattern p f
  twinSL4 : PieceTwinSL4 p f
  twinB : TwinBPartnerPattern p f
  twinSp2 : PieceTwinSp2 p f
  twinTD : PieceTwinTD p f
  twinSU4 : PieceTwinSU4 p f
  multi : MultiPiece p f
  twinClassical : Exotic.MFTwinClassical p f
  twinExc : Exotic.MFTwinExc p f
  orth : RowPiece p f Exotic.ShapeSingleOrth
  singleExc : RowPiece p f Exotic.ShapeSingleExc
  g2d4 : RowPiece p f Exotic.ShapeExoticG2D4
  d4 : RowPiece p f Exotic.ShapeExoticD4

theorem CoreOpenWired₃.upgrade (h : CoreOpenWired₃ p f) : SmallUpgrade p f :=
  Upgrade.smallUpgrade_of_exc2 h.exc h.params

theorem CoreOpenWired₃.pieceExotic (h : CoreOpenWired₃ p f) : PieceExotic p f :=
  (Exotic.ExoticPieces.mk h.twinClassical h.twinExc (rowSp6_of_recognition h.psp6 h.upgrade)
    h.orth h.singleExc h.g2d4 h.d4).pieceExotic

theorem CoreOpenWired₃.bootTriple (hkg8 : Balance.LayerGenerationModel)
    (h : CoreOpenWired₃ p f) : BootTriple p f := by
  by_cases h27 : p ^ f = 27
  · exact h.bootTriple27 h27
  · exact Balance.Bootstrap.bootTriple_of_model_nine h27 hkg8 h.frameMF1 h.frameCoverage
      h.frameLevi

theorem CoreOpenWired₃.toCoreStep (hGH : GH74SectionalModels)
    (hkg8 : Balance.LayerGenerationModel) (h : CoreOpenWired₃ p f) : CoreStep p f := by
  intro hp2 hq G _ _ _ hnab K z hz hBelow
  have hMFZ := Gaps.fundNoncentral p
  have hsect : CITSectionalFour := citSectionalFour_of_gh74_models hGH
  have hshape := shapePiece_of_rows pieceSL7 (pieceSL6_of_five_final hMFZ)
    (rowSLs_of_parts h.sl3 hsect h.upgrade (chainPieceSL45_of_setup hMFZ)) pieceSU7
    (pieceSU6_of_phanE6 hMFZ h.phanE6) (pieceSUs_of_parts hMFZ h.su34) pieceSp4 h.sp3
    (pieceE7_of_exists h.e7) (pieceE8_of_exists h.e8) (rowTwinD_of_pattern hMFZ h.twinD)
    h.twinSL4 (rowTwinB_of_pattern hMFZ h.twinB) h.twinSp2 h.twinTD h.twinSU4
    (shapeExcluded_of_pieces pieceAllA1 (pieceNoA1_of_mfz hMFZ) h.pieceExotic)
  by_cases h2 : CFSG.Open.twoRank G ≤ 2
  · exact h.upgrade G hnab hp2 hq K z hz
      (citRankTwo G hnab z hz.orderOf_eq_two K hz.mem hz.subnormal
        (witness_of_isClassicalMember hp2 hq hz) (not_isSolvable_of_isClassicalMember hz) h2)
  · have h3 : 3 ≤ CFSG.Open.twoRank G := by omega
    by_cases hgen : RouteD.DeltaConnected (𝒞 K) ∧ BootData p f (𝒞 K)
    · exact coreStep_generic (h.bootTriple hkg8) h.bootNoTriple hshape h.multi hnab hp2 hq hz
        hBelow hgen.1 hgen.2
    · exact coreStep_small hsect h.disconnected
        (ConnectedA2.smallConnectedA2_of_inputs h.connectedA2)
        (smallTypeC_of_setup h.typeCSetup hshape h.multi) h.upgrade hnab hp2 hq hz hBelow h3 hgen

theorem citSimplePerfect_of_wired₃ (hGH : GH74SectionalModels)
    (hkg8 : Balance.LayerGenerationModel) (hcore : ∀ (p f : ℕ) [Fact p.Prime], CoreOpenWired₃ p f)
    (GS : Hat2A7.GoldschmidtMilestone) (TW : Hat2A7.TwinExclusion) (BS : Hat2A7.A7BStep) :
    CITSimplePerfect :=
  Generic.citSimplePerfect_of_cases
    (Generic.citSimplePerfectSL2_of_citInductiveU
      (fun p f _ => ModelFacts.citInductiveU_of_coreStep_exc2
        ((hcore p f).toCoreStep hGH hkg8) (hcore p f).exc)
      ModelFacts.modelClauseZero)
    (cit2A7Case_of_inputs GS TW (Hat2A7.localOddCentralStep2A7_of_B BS) Hat2A7.stepReduction2A7)

structure WiredInputs₃ : Prop where
  gh74 : GH74SectionalModels
  kg8 : Balance.LayerGenerationModel
  core : ∀ (p f : ℕ) [Fact p.Prime], CoreOpenWired₃ p f
  goldschmidt : Hat2A7.GoldschmidtMilestone
  twin : Hat2A7.TwinExclusion
  a7B : Hat2A7.A7BStep
  nonTight : PartOneSolvableNonTight
  normalOddByQuaternion : NormalOddByQuaternion

theorem models_of_wired_inputs₃
    (hGH : GH74SectionalModels) (hkg8 : Balance.LayerGenerationModel)
    (hcore : ∀ (p f : ℕ) [Fact p.Prime], CoreOpenWired₃ p f)
    (GS : Hat2A7.GoldschmidtMilestone) (TW : Hat2A7.TwinExclusion) (BS : Hat2A7.A7BStep)
    (hNT : PartOneSolvableNonTight) (hB : NormalOddByQuaternion)
    (G : Type) [Group G] [Finite G]
    [IsSimpleGroup (genFittingFStar G)]
    (hFnonab : ∃ a b : genFittingFStar G, a * b ≠ b * a)
    (z : G) (hz : orderOf z = 2)
    (J : Subgroup G) (hzJ : z ∈ J) (hJ : IsSubnormal J (Subgroup.centralizer ({z} : Set G)))
    (S : Sylow 2 J)
    (hS : ∃ r : ℕ, 3 ≤ r ∧ Nonempty ((S : Subgroup J) ≃* QuaternionGroup (2 ^ (r - 2)))) :
    (classicalInvolutionWitness J → CFSG.Blueprint.OddLieType (genFittingFStar G) ∨
      CFSG.Blueprint.NativeSporadic.IsSporadic (genFittingFStar G) .M11) ∧
    (classicalInvolutionTightlyEmbedded J → CFSG.Blueprint.OddLieType (genFittingFStar G) ∨
      CFSG.Blueprint.NativeSporadic.IsSporadic (genFittingFStar G) .M11 ∨
      CFSG.Blueprint.NativeSporadic.IsSporadic (genFittingFStar G) .M12) :=
  models_of_citSimplePerfect (citSimplePerfect_of_wired₃ hGH hkg8 hcore GS TW BS)
    (partOneSolvable_of_inputs hB hNT) hB G hFnonab z hz J hzJ hJ S hS

theorem order_of_wired_inputs₃
    (hGH : GH74SectionalModels) (hkg8 : Balance.LayerGenerationModel)
    (hcore : ∀ (p f : ℕ) [Fact p.Prime], CoreOpenWired₃ p f)
    (GS : Hat2A7.GoldschmidtMilestone) (TW : Hat2A7.TwinExclusion) (BS : Hat2A7.A7BStep)
    (hNT : PartOneSolvableNonTight) (hB : NormalOddByQuaternion)
    (G : Type) [Group G] [Finite G]
    (F : Subgroup G) [F.Normal] [IsSimpleGroup F]
    (hFnonab : ∃ a b : F, a * b ≠ b * a)
    (hFstar : Subgroup.centralizer (F : Set G) = ⊥)
    (z : G) (hz : orderOf z = 2)
    (J : Subgroup G) (hzJ : z ∈ J) (hJ : IsSubnormal J (Subgroup.centralizer ({z} : Set G)))
    (S : Sylow 2 J)
    (hS : ∃ r : ℕ, 3 ≤ r ∧ Nonempty ((S : Subgroup J) ≃* QuaternionGroup (2 ^ (r - 2)))) :
    (classicalInvolutionWitness J →
      (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ Nat.card F ∈ lieOrdersChar p) ∨ Nonempty (F ≃* M11)) ∧
    (classicalInvolutionTightlyEmbedded J →
      (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ Nat.card F ∈ lieOrdersChar p) ∨ Nonempty (F ≃* M11) ∨
        Nonempty (F ≃* classicalInvolutionM12)) :=
  orderForm_of_modelsForm (fun _ _ h => card_mem_lieOrdersChar_of_oddLieType h)
    (fun G _ _ _ hFnonab z hz J hzJ hJ S hS =>
      models_of_wired_inputs₃ hGH hkg8 hcore GS TW BS hNT hB G hFnonab z hz J hzJ hJ S hS)
    G F hFnonab hFstar z hz J hzJ hJ S hS

theorem WiredInputs₃.models (h : WiredInputs₃)
    (G : Type) [Group G] [Finite G]
    [IsSimpleGroup (genFittingFStar G)]
    (hFnonab : ∃ a b : genFittingFStar G, a * b ≠ b * a)
    (z : G) (hz : orderOf z = 2)
    (J : Subgroup G) (hzJ : z ∈ J) (hJ : IsSubnormal J (Subgroup.centralizer ({z} : Set G)))
    (S : Sylow 2 J)
    (hS : ∃ r : ℕ, 3 ≤ r ∧ Nonempty ((S : Subgroup J) ≃* QuaternionGroup (2 ^ (r - 2)))) :
    (classicalInvolutionWitness J → CFSG.Blueprint.OddLieType (genFittingFStar G) ∨
      CFSG.Blueprint.NativeSporadic.IsSporadic (genFittingFStar G) .M11) ∧
    (classicalInvolutionTightlyEmbedded J → CFSG.Blueprint.OddLieType (genFittingFStar G) ∨
      CFSG.Blueprint.NativeSporadic.IsSporadic (genFittingFStar G) .M11 ∨
      CFSG.Blueprint.NativeSporadic.IsSporadic (genFittingFStar G) .M12) :=
  models_of_wired_inputs₃ h.gh74 h.kg8 h.core h.goldschmidt h.twin h.a7B h.nonTight
    h.normalOddByQuaternion G hFnonab z hz J hzJ hJ S hS

theorem WiredInputs₃.order (h : WiredInputs₃)
    (G : Type) [Group G] [Finite G]
    (F : Subgroup G) [F.Normal] [IsSimpleGroup F]
    (hFnonab : ∃ a b : F, a * b ≠ b * a)
    (hFstar : Subgroup.centralizer (F : Set G) = ⊥)
    (z : G) (hz : orderOf z = 2)
    (J : Subgroup G) (hzJ : z ∈ J) (hJ : IsSubnormal J (Subgroup.centralizer ({z} : Set G)))
    (S : Sylow 2 J)
    (hS : ∃ r : ℕ, 3 ≤ r ∧ Nonempty ((S : Subgroup J) ≃* QuaternionGroup (2 ^ (r - 2)))) :
    (classicalInvolutionWitness J →
      (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ Nat.card F ∈ lieOrdersChar p) ∨ Nonempty (F ≃* M11)) ∧
    (classicalInvolutionTightlyEmbedded J →
      (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ Nat.card F ∈ lieOrdersChar p) ∨ Nonempty (F ≃* M11) ∨
        Nonempty (F ≃* classicalInvolutionM12)) :=
  order_of_wired_inputs₃ h.gh74 h.kg8 h.core h.goldschmidt h.twin h.a7B h.nonTight
    h.normalOddByQuaternion G F hFnonab hFstar z hz J hzJ hJ S hS

end CFSG.ClassicalInvolution.MilestoneAssembly
