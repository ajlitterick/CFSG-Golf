module

public import CFSG.ClassicalInvolution.MilestoneAssembly
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalExc3
public import CFSG.ClassicalInvolution.ModelFacts.FundNoncentralBridge
public import CFSG.ClassicalInvolution.RouteD.GapsFive
public import CFSG.ClassicalInvolution.RouteD.LocalTwinFinal
public import CFSG.ClassicalInvolution.RouteD.SmallAPiece
public import CFSG.ClassicalInvolution.RouteD.TypeEAdapt
public import CFSG.ClassicalInvolution.SmallCases.ConnectedA2
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7LocalB
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.Ly
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Certificates.CosetTableShort
public import CFSG.ClassicalInvolution.ModelFacts.OddCover
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs
public import CFSG.ClassicalInvolution.Models.SymplecticPairs
public import CFSG.ClassicalInvolution.Models.Transfer
public import CFSG.ClassicalInvolution.Models.UnitaryFrames
public import CFSG.ClassicalInvolution.RouteD.LocalTwinBAdapt
public import CFSG.ClassicalInvolution.RouteD.LocalTwinBWeakNodes
public import CFSG.ClassicalInvolution.RouteD.TypeDAdapt
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.J3CheckInputs
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.LyCert
public import CFSG.ClassicalInvolution.SolvableCase
public import CFSG.Goldschmidt.Statements
public import CFSG.Goldschmidt.StatementsG4
public import CFSG.Goldschmidt.StatementsH
public import CFSG.LocalAnalysis.ComponentClassification.BadTwoComponentSubgroup
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddLieClassical
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddLieE6E7Triality
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTISymplectic
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.Milestones.CL_LIT_Goldschmidt_strongly_closed_abelian_models
public import CFSG.Open.GorensteinHaradaSectionalRankFourMilestoneDefs
public import CFSG.Permutation.AlternatingAutomorphism
public import CFSG.Sporadic.Bridge.LyData
public import CFSG.Sporadic.Bridge.M11CheckInputs
public import CFSG.Sporadic.Bridge.TableSurj
public import CFSG.Sporadic.HN.LevelChainSpec
public import CFSG.Sporadic.Ly.ActionBase
public import CFSG.Sporadic.Ly.CertificateBase
public import CFSG.Sporadic.Ly.Simple
public import CFSG.Sporadic.LyBase
public import CFSG.Sporadic.McL
public import CFSG.Sporadic.Presentation.Common
public import CFSG.Sporadic.Presentation.Ly
public import CFSG.Sporadic.Schreier.LyFixedSet
public import CFSG.Walter.J1
public import CFSG.Walter.J1Recog
public import CFSG.Walter.Ree.Thompson2.BaseFin
public import CFSG.Walter.ReeOrder.WardLocal
public import CFSG.Walter.W67.Section8.Prop83
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

namespace CFSG.ClassicalInvolution.MilestoneAssembly

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution CFSG.ClassicalInvolution.RouteD
open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.CoreAssembly
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.Open (genFittingFStar IsSubnormal classicalInvolutionWitness
  classicalInvolutionTightlyEmbedded lieOrdersChar M11 classicalInvolutionM12)

variable {p f : ℕ} [Fact p.Prime]

local notation "𝒞" => Generic.CoreAssembly.conjClass

theorem pieceSL6_of_five_final (hMFZ : Gaps.FundNoncentral p) : PieceSL6 p f := by
  intro a t n hshape G _ _ _ hnab K z S hS
  obtain ⟨rfl, rfl, rfl⟩ := hshape
  have hS5 := localShapeA_of_T (m := 5) hS
  rcases Gaps.routeD_typeA_five_final hMFZ S.odd S.five S.inClass S.exact (mem_conjClass_self K)
    (single_class K) S.conn S.cls hS5 S.p1 with ⟨D, -, -⟩ | ⟨D, -, -⟩
  · exact ⟨D⟩
  · exact ⟨D⟩

theorem chainPieceSL45_of_setup (hMFZ : Gaps.FundNoncentral p) : ChainPieceSL45 p f :=
  fun _ _ _ _ _ _ _ S _ h3 h4 hshape => exists_chain_of_setup hMFZ S h3 h4 hshape

@[expose] def TwinDPartnerPattern (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z → ∀ m : ℕ, 4 ≤ m →
      LocalShapeT p f 2 .POmegaPlus m (𝒞 K) z → ∀ β ∈ 𝒞 K, ∀ t : G,
        IsClassicalMember p f β t →
        (∃ W, LinearBlockStandardPair (GaloisField p f) W K β) →
        HasFixedMember (𝒞 K) K β z → PartnerPatternD p f m (𝒞 K) K β t

@[expose] def TwinBPartnerPattern (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z → ∀ m : ℕ, 3 ≤ m →
      LocalShapeT p f 2 .POmegaOdd m (𝒞 K) z → ∀ β ∈ 𝒞 K, ∀ t : G,
        IsClassicalMember p f β t →
        (∃ W, LinearBlockStandardPair (GaloisField p f) W K β) →
        HasFixedMember (𝒞 K) K β z → PartnerPatternBPair p f m (𝒞 K) K β t

@[expose] def E7PartnerExists (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z →
      LocalShapeT p f 1 .POmegaPlus 6 (𝒞 K) z →
      ∃ j : Fin 6 → Subgroup G, NodeSystem p f (CFSG.Timmesfeld.edgeD 6) (𝒞 K) K z j ∧
        (PartnerAt p f (𝒞 K) j 4 ∨ PartnerAt p f (𝒞 K) j 5)

@[expose] def E8PartnerExists (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z →
      LocalShapeT p f 1 .E7 0 (𝒞 K) z →
      ∃ j : Fin 7 → Subgroup G, NodeSystem p f (CFSG.Timmesfeld.edgeE 7) (𝒞 K) K z j ∧
        PartnerAt p f (𝒞 K) j 6

theorem rowTwinD_of_pattern (hMFZ : Gaps.FundNoncentral p) (h : TwinDPartnerPattern p f) :
    RowPiece p f ShapeTwinD := by
  intro a t n hshape G _ _ _ hnab K z S hS
  obtain ⟨rfl, rfl, hn⟩ := hshape
  have hn' : n + 2 - 2 = n := by omega
  have hS' : LocalShapeT p f 2 .POmegaPlus (n + 2 - 2) (𝒞 K) z := by rw [hn']; exact hS
  obtain ⟨D, -, -⟩ := routeD_typeD_of_partner_pattern hMFZ S.odd S.five (n := n + 2) (by omega)
    S.inClass S.exact (mem_conjClass_self K) (single_class K) S.conn S.cls hS' S.p1 (by
      intro β hβ t ht hKβ hfix
      have := h G hnab K z S n hn hS β hβ t ht hKβ hfix
      rwa [hn'])
  exact ⟨D⟩

theorem rowTwinB_of_pattern (hMFZ : Gaps.FundNoncentral p) (h : TwinBPartnerPattern p f) :
    RowPiece p f ShapeTwinB := by
  intro a t n hshape G _ _ _ hnab K z S hS
  obtain ⟨rfl, rfl, hn⟩ := hshape
  have hn' : n + 2 - 2 = n := by omega
  have hS' : LocalShapeT p f 2 .POmegaOdd (n + 2 - 2) (𝒞 K) z := by rw [hn']; exact hS
  obtain ⟨D, -, -⟩ := routeD_typeB_pair_of_partner_pattern hMFZ S.odd S.five (n := n + 2)
    (by omega) S.inClass S.exact (mem_conjClass_self K) (single_class K) S.conn S.cls hS' S.p1 (by
      intro β hβ t ht hKβ hfix
      have := h G hnab K z S n hn hS β hβ t ht hKβ hfix
      rwa [hn'])
  exact ⟨D⟩

theorem pieceE7_of_exists (h : E7PartnerExists p f) : PieceE7 p f := by
  intro a t n hshape G _ _ _ hnab K z S hS
  obtain ⟨rfl, rfl, rfl⟩ := hshape
  obtain ⟨D, -, -⟩ := routeD_typeE7_of_exists S.odd S.five S.inClass (mem_conjClass_self K)
    (single_class K) S.conn S.cls hS S.p1 (h G hnab K z S hS)
  exact ⟨D⟩

theorem pieceE8_of_exists (h : E8PartnerExists p f) : PieceE8 p f := by
  intro a t n hshape G _ _ _ hnab K z S hS
  obtain ⟨rfl, rfl, rfl⟩ := hshape
  obtain ⟨D, -, -⟩ := routeD_typeE8_of_exists S.odd S.five S.inClass (mem_conjClass_self K)
    (single_class K) S.conn S.cls hS S.p1 (h G hnab K z S hS)
  exact ⟨D⟩

structure CoreOpenWired (p f : ℕ) [Fact p.Prime] : Prop where
  disconnected : SmallDisconnected p f
  connectedA2 : ConnectedA2.ConnectedA2Inputs p f
  typeC : SmallTypeC p f
  upgrade : SmallUpgrade p f
  bootTriple : BootTriple p f
  bootNoTriple : BootNoTriple p f
  sl3 : PieceSL3Big p f
  su6 : PieceSU6 p f
  sus : PieceSUs p f
  sp4P1 : PieceSp4P1 p f
  sp4NoOther : PieceSp4NoOther p f
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
  allA1 : PieceAllA1 p f
  exotic : PieceExotic p f

theorem coreStep_of_wired (hGH : GH74SectionalModels) (h : CoreOpenWired p f) : CoreStep p f := by
  intro hp2 hq G _ _ _ hnab K z hz hBelow
  have hMFZ := Gaps.fundNoncentral p
  have hsect : CITSectionalFour := citSectionalFour_of_gh74_models hGH
  have hshape := shapePiece_of_rows pieceSL7 (pieceSL6_of_five_final hMFZ)
    (rowSLs_of_parts h.sl3 hsect h.upgrade (chainPieceSL45_of_setup hMFZ)) pieceSU7 h.su6 h.sus
    (pieceSp4_of_pieces h.sp4P1 h.sp4NoOther) h.sp3 (pieceE7_of_exists h.e7)
    (pieceE8_of_exists h.e8) (rowTwinD_of_pattern hMFZ h.twinD) h.twinSL4
    (rowTwinB_of_pattern hMFZ h.twinB) h.twinSp2 h.twinTD h.twinSU4
    (shapeExcluded_of_pieces h.allA1 (pieceNoA1_of_mfz hMFZ) h.exotic)
  by_cases h2 : CFSG.Open.twoRank G ≤ 2
  · exact h.upgrade G hnab hp2 hq K z hz
      (citRankTwo G hnab z hz.orderOf_eq_two K hz.mem hz.subnormal
        (witness_of_isClassicalMember hp2 hq hz) (not_isSolvable_of_isClassicalMember hz) h2)
  · have h3 : 3 ≤ CFSG.Open.twoRank G := by omega
    by_cases hgen : RouteD.DeltaConnected (𝒞 K) ∧ BootData p f (𝒞 K)
    · exact coreStep_generic h.bootTriple h.bootNoTriple hshape h.multi hnab hp2 hq hz hBelow
        hgen.1 hgen.2
    · exact coreStep_small hsect h.disconnected
        (ConnectedA2.smallConnectedA2_of_inputs h.connectedA2) h.typeC h.upgrade hnab hp2 hq hz
        hBelow h3 hgen

theorem citSimplePerfect_of_wired (hGH : GH74SectionalModels)
    (hcore : ∀ (p f : ℕ) [Fact p.Prime], CoreOpenWired p f)
    (hexc : ∀ (p f : ℕ) [Fact p.Prime], ModelFacts.ClassicalMembersFundamentalExc3 p f)
    (GS : Hat2A7.GoldschmidtMilestone) (TW : Hat2A7.TwinExclusion) (BS : Hat2A7.A7BStep) :
    CITSimplePerfect :=
  Generic.citSimplePerfect_of_cases
    (Generic.citSimplePerfectSL2_of_citInductiveU
      (fun p f _ => ModelFacts.citInductiveU_of_coreStep_exc3 (coreStep_of_wired hGH (hcore p f))
        (hexc p f))
      ModelFacts.modelClauseZero)
    (cit2A7Case_of_inputs GS TW (Hat2A7.localOddCentralStep2A7_of_B BS) Hat2A7.stepReduction2A7)

structure WiredInputs : Prop where
  gh74 : GH74SectionalModels
  core : ∀ (p f : ℕ) [Fact p.Prime], CoreOpenWired p f
  exc : ∀ (p f : ℕ) [Fact p.Prime], ModelFacts.ClassicalMembersFundamentalExc3 p f
  goldschmidt : Hat2A7.GoldschmidtMilestone
  twin : Hat2A7.TwinExclusion
  a7B : Hat2A7.A7BStep
  nonTight : PartOneSolvableNonTight
  normalOddByQuaternion : NormalOddByQuaternion

theorem models_of_wired_inputs
    (hGH : GH74SectionalModels) (hcore : ∀ (p f : ℕ) [Fact p.Prime], CoreOpenWired p f)
    (hexc : ∀ (p f : ℕ) [Fact p.Prime], ModelFacts.ClassicalMembersFundamentalExc3 p f)
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
  models_of_citSimplePerfect (citSimplePerfect_of_wired hGH hcore hexc GS TW BS)
    (partOneSolvable_of_inputs hB hNT) hB G hFnonab z hz J hzJ hJ S hS

theorem order_of_wired_inputs
    (hGH : GH74SectionalModels) (hcore : ∀ (p f : ℕ) [Fact p.Prime], CoreOpenWired p f)
    (hexc : ∀ (p f : ℕ) [Fact p.Prime], ModelFacts.ClassicalMembersFundamentalExc3 p f)
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
      models_of_wired_inputs hGH hcore hexc GS TW BS hNT hB G hFnonab z hz J hzJ hJ S hS)
    G F hFnonab hFstar z hz J hzJ hJ S hS

theorem WiredInputs.models (h : WiredInputs)
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
  models_of_wired_inputs h.gh74 h.core h.exc h.goldschmidt h.twin h.a7B h.nonTight
    h.normalOddByQuaternion G hFnonab z hz J hzJ hJ S hS

theorem WiredInputs.order (h : WiredInputs)
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
  order_of_wired_inputs h.gh74 h.core h.exc h.goldschmidt h.twin h.a7B h.nonTight
    h.normalOddByQuaternion G F hFnonab hFstar z hz J hzJ hJ S hS

end CFSG.ClassicalInvolution.MilestoneAssembly
