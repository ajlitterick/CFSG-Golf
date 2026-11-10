module

public import CFSG.LocalAnalysis.StandardType.GGF4N2RootAut
import CFSG.LocalAnalysis.StandardType.GGTPNDefs
import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylNoLine
import CFSG.LocalAnalysis.ComponentClassification.Walter86.TableII.Component
public import CFSG.LieType.Chevalley.EvenF4AutomorphismNormalForm
import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.CenterProofFastPart2
public import CFSG.LocalAnalysis.StandardType.GGSixLSixFivePumpup
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Bal209TwoIn
public import CFSG.RankThree.Classical2.SLnFrobeniusFormFixed
public import CFSG.Quasithin.SteinbergBTQuasisimpleSQTKCenter
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphUnitaryLift
public import CFSG.GroupTheory.CardMapInfKer
public import CFSG.Quasithin.Background.F918P4
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommLinTransferLevi
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommLinTransferCover

import CFSG.RankThree.PartTwo.Sec4.T444.Item434CoverKit
import CFSG.RankThree.Coprime.ThompsonElementaryComplement

import CFSG.GroupTheory.SupCommute

import TauCeti.Algebra.Group.Subgroup.ModularLaw
import TauCeti.Algebra.Group.Subgroup.Ker

import CFSG.LocalAnalysis.StandardType.GGSecFiveBProperRootPerm

import all CFSG.RankThree.PartOne.KC.PrimaryDecomposition

public import CFSG.LocalAnalysis.StandardType.GGTypeAFarPComp
public import CFSG.LinearAlgebra.LinearGroups.Perfect

public import CFSG.LocalAnalysis.StandardType.GGF4N2RootCharts
import all CFSG.LocalAnalysis.StandardType.GGF4N2RootCharts

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCTFieldTwist
public import CFSG.CGT.PushingUpLit.CGT6.SixFourU3Alg
public import CFSG.RankThree.PartOne.KC.SymplecticFullCentralizerTransvection

public import CFSG.Assembly.OrderReductions.LinearOrders

public import CFSG.LocalAnalysis.StandardType.GGTriD4NoneTransport

import all CFSG.Fischer.F4
import all CFSG.LocalAnalysis.StandardType.GGF4N2KComponents

public import CFSG.RankThree.Classical.SteinbergBJSymplecticCrossPrimeBlocks
public import CFSG.Fischer.F4
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.DirectProduct

public import CFSG.LieType.Universal.Unitary.Comparison

public import CFSG.Open.StatedSUFieldChange

public import CFSG.LieType.Multipliers.L34Model

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265Std

public import CFSG.LocalAnalysis.StandardType.GGF4N2KComponents

public import CFSG.LocalAnalysis.StandardType.GGF4N2JNative
public import CFSG.LocalAnalysis.StandardType.GGF4N2JModelExclusions
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.ComponentRootSpan
public import CFSG.LocalAnalysis.ComponentInitial.BlockCentralQuotient
public import CFSG.RankThree.CentralLift.ClassicalCenterTrivial
public import CFSG.RankThree.PartOne.CTP.PhanBridge
public import CFSG.GroupTheory.CenterlessInnerCentralizer
public import Mathlib.Algebra.CharP.CharAndCard

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.OmegaFacts2

public import CFSG.Quasithin.EmptyFaithful.SBc17Out5

public import CFSG.LocalAnalysis.OddStandard.AltStdSecLookupEightLinear

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaInputsL44Std

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Classification

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.SecondPointWAux
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRestGen
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCover
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaEndDefs
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaInputsKinds
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaInputsStd
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2015Defs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267Cover
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T156Facts
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T156Layer
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommGeneric
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommLinDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.SecondPointDefs
public import CFSG.Quasithin.EmptyFaithful.S146F13
public import CFSG.Quasithin.EmptyFaithful.S146F16
public import CFSG.Quasithin.EmptyFaithful.S146P10
public import CFSG.Quasithin.EmptyFaithful.S146P13
public import CFSG.Quasithin.EmptyFaithful.S146P17
public import CFSG.Quasithin.EmptyFaithful.S146P20
public import CFSG.Quasithin.EmptyFaithful.SBc14Call

public section

namespace CFSG.StandardType

local notation "V₈[" F "]" => (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F)

open Polynomial Module QuadraticMap CFSG.Open CFSG.Assembly
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal
  CFSG.GroupTheory.WeirSylow CFSG.LieType.Universal.Spin

private lemma subgroupOf_inf_centralizer_eq_centralizer
    {G : Type} [Group G] {K : Subgroup G} {x : G} {a : K} (act : MulAut K)
    (ha : ∀ k : K, a * k * a⁻¹ = act k)
    (hx : ∀ k : K, ((act k : K) : G) = x * (k : G) * x⁻¹) :
    (K ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf K =
      Subgroup.centralizer ({a} : Set K) := by
  ext k
  constructor
  · intro hk
    have hkx : (k : G) * x = x * (k : G) := by
      exact Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_subgroupOf.mp hk).2
    have hfixx : x * (k : G) * x⁻¹ = (k : G) := by
      rw [← hkx]
      group
    have hact : act k = k := by
      apply Subtype.ext
      rw [hx k, hfixx]
    have hfixa : a * k * a⁻¹ = k := by
      rw [ha k, hact]
    have hcomm : k * a = a * k := (mul_inv_eq_iff_eq_mul.mp hfixa).symm
    simpa [Subgroup.mem_centralizer_singleton_iff] using hcomm
  · intro hk
    have hcomm : k * a = a * k :=
      Subgroup.mem_centralizer_singleton_iff.mp hk
    have hfixa : a * k * a⁻¹ = k := by
      rw [← hcomm]
      group
    have hact : act k = k := by
      rw [← ha k]
      exact hfixa
    have hfixx : x * (k : G) * x⁻¹ = (k : G) := by
      have h := congrArg (fun z : K => (z : G)) hact
      simpa [hx k] using h
    have hkx : (k : G) * x = x * (k : G) :=
      (mul_inv_eq_iff_eq_mul.mp hfixx).symm
    exact Subgroup.mem_subgroupOf.mpr
      ⟨k.2, Subgroup.mem_centralizer_singleton_iff.mpr hkx⟩


theorem ggF4N2J_not_psl2_of_card_sixteen
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = 16)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {Rd Ra : Prop} (hR : GGSecFiveRestGen 5 B Bs x L D J Rd Ra)
    (hL : GGCentralImage .POmegaMinus 4 2 L) :
    IsEmpty (↥J ⧸ Subgroup.center ↥J ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI := Fintype.ofFinite F
  letI := Fintype.ofFinite (GaloisField 2 4)
  let κ : F ≃+* GaloisField 2 4 := FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      GaloisField.card 2 4 (by decide), hF]
    norm_num)
  obtain ⟨e⟩ := CFSG.RankThree.PartOne.CTP.nonempty_sl_equiv_of_ringEquiv κ 2
  let eQ : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 4) :=
    QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)
  exact ⟨fun eJ => (ggF4N2J_not_psl216 hR hL).false (eJ.trans eQ)⟩

theorem ggF4N2J_native_positions_of_model
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {Rd Ra : Prop} (hR : GGSecFiveRestGen 5 B Bs x L D J Rd Ra)
    (hL : GGCentralImage .POmegaMinus 4 2 L)
    {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 4)
    {b c : F} (hbc : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (θ : L ≃* ProjOrthDerived (quadMinus 4 F b c)) :
    ∃ d ∈ D, d ∉ Subgroup.zpowers x ∧ ∃ a : L, orderOf a = 5 ∧
        (∀ l : L, d * (l : G) * d⁻¹ = ((a * l * a⁻¹ : L) : G)) ∧
        (Subgroup.centralizer ({a} : Set L)).map L.subtype =
          L ⊓ Subgroup.centralizer (D : Set G) ∧
        (J.subgroupOf L).map θ.toMonoidHom =
          LargeEvenLayer (Subgroup.centralizer ({θ a} :
            Set (ProjOrthDerived (quadMinus 4 F b c)))) ∧
        ∃ (u : ↥(orthDerived (quadMinus 4 F b c)))
          (hu : OddOrderIsometry (quadMinus 4 F b c) 5
            (u : V₈[F] ≃ₗ[F] V₈[F])), QuotientGroup.mk u = θ a ∧
          ((∃ h ∈ primaryFactors (u : V₈[F] ≃ₗ[F] V₈[F]).toLinearMap, h ≠ X - 1 ∧
              primaryMultiplicity (u : V₈[F] ≃ₗ[F] V₈[F]).toLinearMap h = 3 ∧
              CFSG.IsQuasisimple ↥(specialBlock (quadMinus 4 F b c) (u : V₈[F] ≃ₗ[F] V₈[F]) h) ∧
              (J.subgroupOf L).map θ.toMonoidHom =
                componentImage (quadMinus 4 F b c) (u : V₈[F] ≃ₗ[F] V₈[F]) h) ∨
            (finrank F (fixedSpace (u : V₈[F] ≃ₗ[F] V₈[F])) = 6 ∧
              IsPlusType ((quadMinus 4 F b c).comp (fixedSpace (u : V₈[F] ≃ₗ[F] V₈[F])).subtype) ∧
              (J.subgroupOf L).map θ.toMonoidHom =
                fixedComponentImage (quadMinus 4 F b c) (u : V₈[F] ≃ₗ[F] V₈[F]))) := by
  classical
  obtain ⟨d, hdD, hdx, a, ha, hCa, hJCa, hJE, hact⟩ :=
    ggF4N2J_singleton_centralizer hR hL
  have hJL : J ≤ L := hR.1.2.2.1.2.2.2.2.2.1.1.trans inf_le_left
  let eJ : ↥J ≃* ↥((J.subgroupOf L).map θ.toMonoidHom) :=
    (Subgroup.subgroupOfEquivOfLe hJL).symm.trans
      ((J.subgroupOf L).equivMapOfInjective θ.toMonoidHom θ.injective)
  let eJQ := QuotientGroup.congr _ _ eJ (Subgroup.map_center_eq eJ)
  have hJ' := CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_of_injective
    hJCa θ.toMonoidHom θ.injective
  rw [CFSG.LocalAnalysis.ComponentInitial.map_centralizer_singleton_mulEquiv] at hJ'
  have hJLlayer : J.subgroupOf L = LargeEvenLayer (Subgroup.centralizer ({a} : Set L)) := by
    apply Subgroup.map_injective L.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hJL]
    exact hJE
  have hJlayer : (J.subgroupOf L).map θ.toMonoidHom =
      LargeEvenLayer (Subgroup.centralizer ({θ a} : Set (ProjOrthDerived (quadMinus 4 F b c)))) := by
    rw [hJLlayer, ← largeEvenLayer_map_of_injective _ θ.injective,
      CFSG.LocalAnalysis.ComponentInitial.map_centralizer_singleton_mulEquiv]
  obtain ⟨hQ, hT⟩ := CFSG.ClassicalGroups.Orthogonal.regular_quadMinus (by norm_num : 4 ≤ 4) hbc
  have hm := CFSG.GroupTheory.WeirSylow.not_isPlusType_quadMinus (by norm_num : 1 ≤ 4) hbc
  have ha5 : (θ a) ^ 5 = 1 := by rw [← map_pow, ← ha, pow_orderOf_eq_one a, map_one]
  have ha1 : θ a ≠ 1 := by
    intro h
    have ha1 : a = 1 := θ.injective (h.trans (map_one θ).symm)
    rw [ha1, orderOf_one] at ha
    norm_num at ha
  have hdim : finrank F (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) = 8 := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp
  obtain ⟨u, hu, hua, hpos⟩ := N2Orthogonal.component_cases_of_not_sl2 hQ hT
    (by simpa using hF) hdim hm (θ a) ha5 ha1 ((J.subgroupOf L).map θ.toMonoidHom)
    ((isComponentOf_iff_open).mp hJ')
    (fun F _ _ hF => ⟨fun ε => (ggF4N2J_not_psl24 hF hR hL).false (eJQ.trans ε)⟩)
    (fun F _ _ hF => ⟨fun ε => (ggF4N2J_not_psl2_of_card_sixteen hF hR hL).false (eJQ.trans ε)⟩)
  exact ⟨d, hdD, hdx, a, ha, hact, hCa, hJlayer, u, hu, hua, hpos⟩


theorem ggF4N2_innerRepresentative_mem_plane
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {Rd Ra : Prop} (hR : GGSecFiveRestGen 5 B Bs x L D J Rd Ra)
    (hL : GGCentralImage .POmegaMinus 4 2 L) {d : G} (hdD : d ∈ D)
    (a : L) (ha : orderOf a = 5)
    (hact : ∀ l : L, d * (l : G) * d⁻¹ = ((a * l * a⁻¹ : L) : G)) :
    (a : G) ∈ D := by
  have hcfg := hR.1
  have hpre := hcfg.2.2.1
  have hZ := ggN2Center_eq_bot_of_centralImage hL
  have hBsN : Bs ≤ Subgroup.normalizer (L : Set G) :=
    GGDichotomy.le_normalizer_of_innerDiagOn hR.2.2.1.1
  have hBsEl : IsElemAbelian 5 Bs := hcfg.2.1.2.1
  have hdBs : d ∈ Bs := hcfg.2.1.1 (hpre.1 hdD)
  let dB : Bs := ⟨d, hdBs⟩
  have hα : ggGamma L hBsN dB = MulAut.conj a := by
    ext l
    simpa [dB, ggGamma_coe, MulAut.conj_apply] using hact l
  have haCBs : (a : G) ∈ Subgroup.centralizer (Bs : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    let bB : Bs := ⟨b, hb⟩
    let β : MulAut L := ggGamma L hBsN bB
    have hbcomm : bB * dB = dB * bB := Subtype.ext (hBsEl.comm hb hdBs)
    have hcomm : β * MulAut.conj a = MulAut.conj a * β := by
      rw [← hα]
      exact (map_mul (ggGamma L hBsN) bB dB).symm.trans
        ((congrArg (ggGamma L hBsN) hbcomm).trans (map_mul (ggGamma L hBsN) dB bB))
    have hmem : MulAut.conj a ∈
        CFSG.HardMathSupport.Solomon.LocalBalance.innerAut L ⊓
          Subgroup.centralizer ({β} : Set (MulAut L)) :=
      ⟨⟨a, rfl⟩, Subgroup.mem_centralizer_singleton_iff.mpr hcomm.symm⟩
    rw [CFSG.innerAut_inf_centralizer_eq_map_eqLocus hZ] at hmem
    obtain ⟨a', ha', heq⟩ := Subgroup.mem_map.mp hmem
    have haa : a' = a := CFSG.mulAutConj_injective_of_center_eq_bot hZ heq
    subst a'
    change β a = a at ha'
    have hfix : b * (a : G) * b⁻¹ = a := by
      simpa [β, bB, ggGamma_coe] using congrArg Subtype.val ha'
    exact (mul_inv_eq_iff_eq_mul).mp hfix
  have ha5 : (a : G) ^ 5 = 1 := by
    have h : a ^ 5 = 1 := by rw [← ha]; exact pow_orderOf_eq_one a
    exact congrArg Subtype.val h
  have haBs : (a : G) ∈ Bs := hcfg.2.1.2.2.2 a haCBs ha5
  have hB : B = Bs := Subgroup.eq_of_le_of_card_ge hcfg.2.1.1 (by
    have h := ggF4N2Rank hR hL
    rw [h.1, h.2.1])
  have hJL : J ≤ L := hpre.2.2.2.2.2.1.1.trans inf_le_left
  have hdCJ : d ∈ Subgroup.centralizer (J : Set G) := by
    rw [hpre.2.2.2.2.2.2] at hdD
    exact hdD.2
  have haCJ : (a : G) ∈ Subgroup.centralizer (J : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    have hfixd : d * j * d⁻¹ = j := by
      rw [(Subgroup.mem_centralizer_iff.mp hdCJ j hj).symm]
      group
    have hfixa : (a : G) * j * (a : G)⁻¹ = j :=
      (hact ⟨j, hJL hj⟩).symm.trans hfixd
    exact ((mul_inv_eq_iff_eq_mul).mp hfixa).symm
  rw [hpre.2.2.2.2.2.2]
  refine ⟨?_, haCJ⟩
  change (a : G) ∈ B
  rw [hB]
  exact haBs

theorem ggF4N2J_plane_basis
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {Rd Ra : Prop} (hR : GGSecFiveRestGen 5 B Bs x L D J Rd Ra)
    (hL : GGCentralImage .POmegaMinus 4 2 L) :
    ∃ a : L, (a : G) ∈ D ∧ orderOf a = 5 ∧
      D = Subgroup.zpowers x ⊔ Subgroup.zpowers (a : G) ∧
      CFSG.Assembly.IsComponentOf (J.subgroupOf L) (Subgroup.centralizer ({a} : Set L)) ∧
      J = (LargeEvenLayer (Subgroup.centralizer ({a} : Set L))).map L.subtype := by
  obtain ⟨d, hdD, -, a, ha, -, hJCa, hJE, hact⟩ := ggF4N2J_singleton_centralizer hR hL
  have haD := ggF4N2_innerRepresentative_mem_plane hR hL hdD a ha hact
  have hpre := hR.1.2.2.1
  obtain ⟨-, -, -, -, -, -, hS, -⟩ := hR.1.1
  have hZ := ggN2Center_eq_bot_of_centralImage hL
  have hxC : x ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact Subgroup.mem_centralizer_singleton_iff.mp (hS.2.2.2.1.1 hl)
  have haNot : (a : G) ∉ Subgroup.zpowers x := by
    intro h
    have haC : (a : G) ∈ Subgroup.centralizer (L : Set G) :=
      (Subgroup.zpowers_le.mpr hxC) h
    have haZ : a ∈ Subgroup.center L := by
      rw [Subgroup.mem_center_iff]
      intro l
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp haC l l.2)
    rw [hZ] at haZ
    have ha1 : a = 1 := Subgroup.mem_bot.mp haZ
    rw [ha1, orderOf_one] at ha
    norm_num at ha
  have hD := eq_sup_zpowers_of_card Nat.prime_five hpre.2.1 hpre.2.2.1 hpre.2.2.2.1
    hS.2.2.1 haD haNot
  exact ⟨a, haD, ha, hD, hJCa, hJE⟩

theorem ggF4N2J_statedSU_of_native_block
    {G : Type} [Group G] {L J : Subgroup G} (hJL : J ≤ L)
    {K : Type} [Field K] [Finite K] [CharP K 2]
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Nontrivial V]
    {Q : QuadraticForm K V} (hQ : (polarBilin Q).Nondegenerate) (hK : Nat.card K = 4)
    {v : V ≃ₗ[K] V} (hv : OddOrderIsometry Q 5 v)
    {h : K[X]} (hh : h ∈ primaryFactors v.toLinearMap) (hne : h ≠ X - 1)
    (hq : CFSG.IsQuasisimple ↥(specialBlock Q v h))
    (hm : primaryMultiplicity v.toLinearMap h = 3)
    (θ : ↥L ≃* ProjOrthDerived Q)
    (hJ : (J.subgroupOf L).map θ.toMonoidHom = componentImage Q v h) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2), Nat.card F = 16 ∧
      Nonempty (↥J ≃* ↥(StatedSU 3 4 F)) := by
  obtain ⟨F, _, _, _, hF, ⟨e⟩⟩ :=
    N2Orthogonal.componentImage_statedSU_of_multiplicity_three hQ hK hv hh hne hq hm
  let eJ : ↥J ≃* ↥((J.subgroupOf L).map θ.toMonoidHom) :=
    (Subgroup.subgroupOfEquivOfLe hJL).symm.trans
      ((J.subgroupOf L).equivMapOfInjective θ.toMonoidHom θ.injective)
  exact ⟨F, inferInstance, inferInstance, inferInstance, hF,
    ⟨eJ.trans ((MulEquiv.subgroupCongr hJ).trans e)⟩⟩


open CFSG.LieType.Universal.Unitary

theorem ggF4N2J_centralImage_PSL4
    {G : Type} [Group G] {J : Subgroup G} {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 4)
    (eJ : ↥J ≃* Matrix.SpecialLinearGroup (Fin 4) F) :
    GGCentralImage .PSL 4 2 J := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  letI : Fintype (GaloisField 2 2) := Fintype.ofFinite _
  let eField : GaloisField 2 2 ≃+* F :=
    FiniteField.ringEquivOfCardEq (by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
        GaloisField.card 2 2 (by norm_num), hF]
      norm_num)
  let eU : (ggU .PSL 4 2).K ≃*
      Matrix.SpecialLinearGroup (Fin 4) (GaloisField 2 2) := MulEquiv.refl _
  let eSL : Matrix.SpecialLinearGroup (Fin 4) (GaloisField 2 2) ≃*
      Matrix.SpecialLinearGroup (Fin 4) F :=
    CFSG.LieType.Multipliers.L34.slEquiv (Fin 4) eField
  let ψ : (ggU .PSL 4 2).K →* G :=
    J.subtype.comp (eJ.symm.toMonoidHom.comp ((eU.trans eSL).toMonoidHom))
  have hψinj : Function.Injective ψ :=
    J.subtype_injective.comp (eJ.symm.injective.comp (eU.trans eSL).injective)
  have hψrange : ψ.range = J := by
    have h1 : (eU.trans eSL).toMonoidHom.range = ⊤ := (eU.trans eSL).range_eq_top
    have h2 : eJ.symm.toMonoidHom.range = ⊤ := eJ.symm.range_eq_top
    rw [MonoidHom.range_comp, MonoidHom.range_comp, h1, Subgroup.map_top, h2,
      Subgroup.map_top]
    simp
  refine ⟨ψ, ?_, ?_, hψrange⟩
  · unfold StatedLieAdmissible
    decide
  · rw [MonoidHom.ker_eq_bot ψ hψinj]
    exact bot_le

theorem ggF4N2J_centralImage_PSU3
    {G : Type} [Group G] {J : Subgroup G} {E : Type} [Field E] [Finite E] [CharP E 2]
    (hE : Nat.card E = 16)
    (eJ : ↥J ≃* ↥(StatedSU 3 4 E)) :
    GGCentralImage .PSU 3 2 J := by
  classical
  letI : Fintype E := Fintype.ofFinite E
  letI : Fintype (GaloisField 2 4) := Fintype.ofFinite _
  have hGF : Nat.card (GaloisField 2 4) = (2 ^ 2) ^ 2 := by
    rw [GaloisField.card 2 4 (by norm_num)]
    norm_num
  haveI : CharP (GaloisField 2 4) 2 := by
    exact charP_of_card_eq_prime_pow (p := 2) (f := 4) (by
      rw [Fintype.card_eq_nat_card, GaloisField.card 2 4 (by norm_num)])
  let eField : GaloisField 2 4 ≃+* E :=
    FiniteField.ringEquivOfCardEq (by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
        GaloisField.card 2 4 (by norm_num), hE]
      norm_num)
  let eU : (ggU .PSU 3 2).K ≃*
      SU (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 4) 2 2) 3 :=
    MulEquiv.refl _
  let eStated : SU (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 4) 2 2) 3 ≃*
      StatedSU 3 4 (GaloisField 2 4) :=
    equivStatedSU (p := 2) (f := 2) hGF 3
  let eFieldSU : StatedSU 3 4 (GaloisField 2 4) ≃* StatedSU 3 4 E :=
    CFSG.Open.StatedSUFieldChange.statedSUEquiv eField 3 4
  let eUniv : (ggU .PSU 3 2).K ≃* StatedSU 3 4 E :=
    eU.trans (eStated.trans eFieldSU)
  let ψ : (ggU .PSU 3 2).K →* G :=
    J.subtype.comp (eJ.symm.toMonoidHom.comp eUniv.toMonoidHom)
  have hψinj : Function.Injective ψ :=
    J.subtype_injective.comp (eJ.symm.injective.comp eUniv.injective)
  have hψrange : ψ.range = J := by
    have h1 : eUniv.toMonoidHom.range = ⊤ := eUniv.range_eq_top
    have h2 : eJ.symm.toMonoidHom.range = ⊤ := eJ.symm.range_eq_top
    rw [MonoidHom.range_comp, MonoidHom.range_comp, h1, Subgroup.map_top, h2,
      Subgroup.map_top]
    simp
  refine ⟨ψ, ?_, ?_, hψrange⟩
  · unfold StatedLieAdmissible
    decide
  · rw [MonoidHom.ker_eq_bot ψ hψinj]
    exact bot_le


private theorem GGCentralImage_subgroupOf_of_le
    {G : Type} [Group G] {J K : Subgroup G} (hJK : J ≤ K)
    {t : StatedLieTag} {n f : ℕ}
    (h : CFSG.StandardType.GGCentralImage t n f J) :
    CFSG.StandardType.GGCentralImage t n f (J.subgroupOf K) := by
  classical
  obtain ⟨ψ, hadm, hker, hrange⟩ := h
  let ψK : (CFSG.StandardType.ggU t n f).K →* K :=
    ψ.codRestrict K fun u => by
      have hu : ψ u ∈ J := by rw [← hrange]; exact ⟨u, rfl⟩
      exact hJK hu
  refine ⟨ψK, hadm, ?_, ?_⟩
  · rw [show ψK.ker = ψ.ker from MonoidHom.ker_codRestrict _ _ _]
    exact hker
  · have hsub : ψ.range.subgroupOf K = ψK.range :=
      MonoidHom.subgroupOf_range_eq_of_le ψ (by rw [hrange]; exact hJK)
    rw [hrange] at hsub
    exact hsub.symm


theorem ggF4N2J_isComponentOf_actual_lift_centralizer
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G}
    {Rd Ra : Prop} (hR : GGSecFiveRestGen 5 B Bs x L D J Rd Ra)
    (hNbr : GGNbr 5 B x D J y K)
    (hL : GGCentralImage .POmegaMinus 4 2 L)
    (hK : GGCentralImage .PSL 6 2 K)
    (ψ : Matrix.SpecialLinearGroup (Fin 6) (GaloisField 2 2) →* K)
    (rho : Bs →* Matrix.SpecialLinearGroup (Fin 6) (GaloisField 2 2))
    (hPoint : ∀ (b : Bs) (k : K), ψ (rho b) * k * (ψ (rho b))⁻¹ =
      (K.normalizerMonoidHom.comp
        (Subgroup.inclusion (ggF4N2_Bs_le_normalizer_K hR hNbr hL))) b k)
    (hxBs : x ∈ Bs) :
    CFSG.Assembly.IsComponentOf (J.subgroupOf K)
      (Subgroup.centralizer ({ψ (rho ⟨x, hxBs⟩)} : Set K)) := by
  let action : Bs →* MulAut K :=
    K.normalizerMonoidHom.comp
      (Subgroup.inclusion (ggF4N2_Bs_le_normalizer_K hR hNbr hL))
  let a := rho ⟨x, hxBs⟩
  have hxact : ∀ k : K,
      ((action ⟨x, hxBs⟩ k : K) : G) = x * (k : G) * x⁻¹ := by
    have hact : action = CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.actK
        (ggF4N2_Bs_le_normalizer_K hR hNbr hL) := rfl
    intro k
    rw [hact]
    exact CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.coe_actK
      (ggF4N2_Bs_le_normalizer_K hR hNbr hL) ⟨x, hxBs⟩ k
  have hcent : (K ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf K =
      Subgroup.centralizer ({ψ a} : Set K) :=
    subgroupOf_inf_centralizer_eq_centralizer (action ⟨x, hxBs⟩)
      (fun k => hPoint ⟨x, hxBs⟩ k) hxact
  have hJcompG : CFSG.Assembly.IsComponentOf J
      (K ⊓ Subgroup.centralizer ({x} : Set G)) :=
    ggF4N2J_isComponentOf_K_inf_centralizer_x hR hNbr hL hK
  have hJcompOpen : CFSG.Open.IsComponentOf (J.subgroupOf K)
      ((K ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf K) :=
    CFSG.LocalAnalysis.GLTheoremA.S265.isComponentOf_subgroupOf inf_le_left
      (CFSG.Assembly.isComponentOf_iff_open.mp hJcompG)
  have hJcompK : CFSG.Assembly.IsComponentOf (J.subgroupOf K)
      ((K ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf K) :=
    (CFSG.Assembly.isComponentOf_iff_open).mpr hJcompOpen
  simpa [hcent] using hJcompK

theorem ggF4N2J_not_PSU_three_two
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G}
    {Rd Ra : Prop} (hR : GGSecFiveRestGen 5 B Bs x L D J Rd Ra)
    (hNbr : GGNbr 5 B x D J y K)
    (hL : GGCentralImage .POmegaMinus 4 2 L)
    (hK : GGCentralImage .PSL 6 2 K) : ¬ GGCentralImage .PSU 3 2 J := by
  classical
  obtain ⟨hxBs, hxnot, -, -, -, -⟩ := ggF4N2_x_data hR hNbr
  obtain ⟨ψ, hψSurj, hψKer, rho, hConj, hPoint, hPow, hRhoKer, hCardRange⟩ :=
    ggF4N2_exists_universal_action_lift hR hNbr hL hK
  let action : Bs →* MulAut K :=
    K.normalizerMonoidHom.comp
      (Subgroup.inclusion (ggF4N2_Bs_le_normalizer_K hR hNbr hL))
  let a : Matrix.SpecialLinearGroup (Fin 6) (GaloisField 2 2) :=
    rho ⟨x, hxBs⟩
  have ha5 : a ^ 5 = 1 := hPow ⟨x, hxBs⟩
  have hane : a ≠ 1 := by
    intro ha1
    have hxker : (⟨x, hxBs⟩ : Bs) ∈ rho.ker := by
      rw [MonoidHom.mem_ker]
      exact ha1
    have hxsub : (⟨x, hxBs⟩ : Bs) ∈ (Subgroup.zpowers y).subgroupOf Bs := by
      rwa [← hRhoKer]
    exact hxnot (Subgroup.mem_subgroupOf.mp hxsub)
  have haord : orderOf a = 5 := orderOf_eq_prime ha5 hane
  have hF4 : Nat.card (GaloisField 2 2) = 4 := by
    simpa using GaloisField.card 2 2 (by norm_num)
  have hJK : J ≤ K := ggF4N2J_le_psl6_neighbor hR hNbr hL hK
  have hHcomp : CFSG.Assembly.IsComponentOf (J.subgroupOf K)
      (Subgroup.centralizer ({ψ a} : Set K)) :=
    ggF4N2J_isComponentOf_actual_lift_centralizer hR hNbr hL hK ψ rho hPoint hxBs
  intro hJPSU
  have hHimage : GGCentralImage .PSU 3 2 (J.subgroupOf K) :=
    GGCentralImage_subgroupOf_of_le hJK hJPSU
  exact CFSG.StandardType.not_GGCentralImage_PSU_three_two_of_component
    (F := GaloisField 2 2) (Q := K) (ψ := ψ) hF4 hψKer
    (MonoidHom.range_eq_top.mpr hψSurj) haord hHcomp hHimage

theorem ggF4N2J_native_fixed_plus_six_of_model
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G}
    {Rd Ra : Prop} (hR : GGSecFiveRestGen 5 B Bs x L D J Rd Ra) (hNbr : GGNbr 5 B x D J y K)
    (hL : GGCentralImage .POmegaMinus 4 2 L) (hK : GGCentralImage .PSL 6 2 K)
    {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 4)
    {b c : F} (hbc : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (θ : L ≃* ProjOrthDerived (quadMinus 4 F b c)) :
    ∃ d ∈ D, d ∉ Subgroup.zpowers x ∧ ∃ a : L, orderOf a = 5 ∧
        (∀ l : L, d * (l : G) * d⁻¹ = ((a * l * a⁻¹ : L) : G)) ∧
        (Subgroup.centralizer ({a} : Set L)).map L.subtype =
          L ⊓ Subgroup.centralizer (D : Set G) ∧
        (J.subgroupOf L).map θ.toMonoidHom =
          LargeEvenLayer (Subgroup.centralizer ({θ a} :
            Set (ProjOrthDerived (quadMinus 4 F b c)))) ∧
        ∃ (u : ↥(orthDerived (quadMinus 4 F b c)))
          (hu : OddOrderIsometry (quadMinus 4 F b c) 5
            (u : (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) ≃ₗ[F] (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F))),
          QuotientGroup.mk u = θ a ∧
          Module.finrank F (fixedSpace
            (u : (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) ≃ₗ[F] (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F))) = 6 ∧
          IsPlusType ((quadMinus 4 F b c).comp (fixedSpace
            (u : (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) ≃ₗ[F] (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F))).subtype) ∧
          (J.subgroupOf L).map θ.toMonoidHom =
            fixedComponentImage (quadMinus 4 F b c)
              (u : (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) ≃ₗ[F] (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F)) := by
  classical
  have hnotPSU := ggF4N2J_not_PSU_three_two hR hNbr hL hK
  obtain ⟨d, hdD, hdx, a, ha, hact, hCa, hJlayer, u, hu, hua, hpos⟩ :=
    ggF4N2J_native_positions_of_model hR hL hF hbc θ
  have hJL : J ≤ L := hR.1.2.2.1.2.2.2.2.2.1.1.trans inf_le_left
  have hQ : (QuadraticMap.polarBilin (quadMinus 4 F b c)).Nondegenerate :=
    nondegenerate_polarBilin_quadMinus_of_finite 4 F hbc
  rcases hpos with ⟨h, hh, hne, hm, hq, hJeq⟩ | hfixed
  · obtain ⟨E, hFieldE, hFiniteE, hCharE, hE, ⟨eSU⟩⟩ :=
      ggF4N2J_statedSU_of_native_block hJL hQ hF hu hh hne hq hm θ hJeq
    letI : Field E := hFieldE
    letI : Finite E := hFiniteE
    letI : CharP E 2 := hCharE
    exact False.elim (hnotPSU (ggF4N2J_centralImage_PSU3 hE eSU))
  · exact ⟨d, hdD, hdx, a, ha, hact, hCa, hJlayer, u, hu, hua, hfixed⟩

theorem ggF4N2J_native_fixed_plus_six
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G}
    {Rd Ra : Prop} (hR : GGSecFiveRestGen 5 B Bs x L D J Rd Ra)
    (hNbr : GGNbr 5 B x D J y K)
    (hL : GGCentralImage .POmegaMinus 4 2 L)
    (hK : GGCentralImage .PSL 6 2 K) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2), Nat.card F = 4 ∧
      ∃ b c : F, (∀ s : F, s ^ 2 + b * s + c ≠ 0) ∧
      ∃ θ : ↥L ≃* ProjOrthDerived (quadMinus 4 F b c),
      ∃ d ∈ D, d ∉ Subgroup.zpowers x ∧ ∃ a : L, orderOf a = 5 ∧
        (∀ l : L, d * (l : G) * d⁻¹ = ((a * l * a⁻¹ : L) : G)) ∧
        (Subgroup.centralizer ({a} : Set L)).map L.subtype =
          L ⊓ Subgroup.centralizer (D : Set G) ∧
        (J.subgroupOf L).map θ.toMonoidHom =
          LargeEvenLayer (Subgroup.centralizer ({θ a} :
            Set (ProjOrthDerived (quadMinus 4 F b c)))) ∧
        ∃ (u : ↥(orthDerived (quadMinus 4 F b c)))
          (hu : OddOrderIsometry (quadMinus 4 F b c) 5
            (u : (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) ≃ₗ[F] (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F))),
          QuotientGroup.mk u = θ a ∧
          Module.finrank F (fixedSpace
            (u : (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) ≃ₗ[F] (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F))) = 6 ∧
          IsPlusType ((quadMinus 4 F b c).comp (fixedSpace
            (u : (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) ≃ₗ[F] (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F))).subtype) ∧
          (J.subgroupOf L).map θ.toMonoidHom =
            fixedComponentImage (quadMinus 4 F b c)
              (u : (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) ≃ₗ[F] (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F)) := by
  classical
  have hZ := ggN2Center_eq_bot_of_centralImage hL
  let eQ : (↥L ⧸ Subgroup.center ↥L) ≃* L :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  obtain ⟨-, F, _, _, hF, b, c, hbc, ⟨e⟩⟩ := ggN2Model_of_centralImage hL eQ
  haveI : CharP F 2 :=
    CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434.Cl.charP_two_of_card_four
      (by simpa using hF)
  obtain ⟨e₂⟩ := CFSG.RankThree.CentralLift.nonempty_statedProj_mulEquiv_projOrthDerived
    (coe_quadMinus 4 F b c)
  let θ : ↥L ≃* ProjOrthDerived (quadMinus 4 F b c) := e.trans e₂
  obtain ⟨d, hdD, hdx, a, ha, hact, hCa, hJlayer, u, hu, hua, hfixed⟩ :=
    ggF4N2J_native_fixed_plus_six_of_model hR hNbr hL hK (by simpa using hF) hbc θ
  exact ⟨F, inferInstance, inferInstance, inferInstance, by simpa using hF,
    b, c, hbc, θ, d, hdD, hdx, a, ha, hact, hCa, hJlayer, u, hu, hua, hfixed⟩

theorem ggF4N2J_original_mixed_recognition
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G}
    {Rd Ra : Prop} (hR : GGSecFiveRestGen 5 B Bs x L D J Rd Ra)
    (hNbr : GGNbr 5 B x D J y K)
    (hL : GGCentralImage .POmegaMinus 4 2 L)
    (hK : GGCentralImage .PSL 6 2 K) :
    (¬ GGCentralImage .PSU 3 2 J) ∧
      (∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
        Nat.card F = 4 ∧ Nonempty (↥J ≃* Matrix.SpecialLinearGroup (Fin 4) F)) ∧
      GGCentralImage .PSL 4 2 J := by
  classical
  have hnotPSU := ggF4N2J_not_PSU_three_two hR hNbr hL hK
  obtain ⟨F, hField, hFinite, hChar, hF, b, c, hbc, θ, d, hdD, hdx,
    a, ha, hact, hCa, hJlayer, u, hu, hua, h6, hplus, hJeq⟩ :=
    ggF4N2J_native_fixed_plus_six hR hNbr hL hK
  letI : Field F := hField
  letI : Finite F := hFinite
  letI : CharP F 2 := hChar
  let V := Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F
  let Q : QuadraticForm F V := quadMinus 4 F b c
  have hQ : (QuadraticMap.polarBilin Q).Nondegenerate :=
    nondegenerate_polarBilin_quadMinus_of_finite 4 F hbc
  have hdim : Module.finrank F V = 8 := by simp [V]
  have hJL : J ≤ L := hR.1.2.2.1.2.2.2.2.2.1.1.trans inf_le_left
  let eJ0 : ↥J ≃* ↥((J.subgroupOf L).map θ.toMonoidHom) :=
    (Subgroup.subgroupOfEquivOfLe hJL).symm.trans
      ((J.subgroupOf L).equivMapOfInjective θ.toMonoidHom θ.injective)
  let eSL : ↥(fixedComponentImage Q (u : V ≃ₗ[F] V)) ≃*
      Matrix.SpecialLinearGroup (Fin 4) F :=
    N2Orthogonal.fixedPlusSixMarking hQ hdim hF hu h6 hplus rfl
      (fixedComponentImage Q (u : V ≃ₗ[F] V)) rfl
  let eJ : ↥J ≃* Matrix.SpecialLinearGroup (Fin 4) F :=
    eJ0.trans ((MulEquiv.subgroupCongr hJeq).trans eSL)
  exact ⟨hnotPSU, ⟨F, hField, hFinite, hChar, hF, ⟨eJ⟩⟩,
    ggF4N2J_centralImage_PSL4 hF eJ⟩


theorem ggF4N2J_fixedMultiplicity_of_actual_lift
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G}
    {Rd Ra : Prop} (hR : GGSecFiveRestGen 5 B Bs x L D J Rd Ra)
    (hNbr : GGNbr 5 B x D J y K)
    (hL : GGCentralImage .POmegaMinus 4 2 L)
    (hK : GGCentralImage .PSL 6 2 K)
    (ψ : Matrix.SpecialLinearGroup (Fin 6) (GaloisField 2 2) →* K)
    (rho : Bs →* Matrix.SpecialLinearGroup (Fin 6) (GaloisField 2 2))
    (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin 6) (GaloisField 2 2)))
    (hPoint : ∀ (b : Bs) (k : K), ψ (rho b) * k * (ψ (rho b))⁻¹ =
      (K.normalizerMonoidHom.comp
        (Subgroup.inclusion (ggF4N2_Bs_le_normalizer_K hR hNbr hL))) b k)
    (hPow : ∀ b : Bs, (rho b) ^ 5 = 1)
    (hRhoKer : rho.ker = (Subgroup.zpowers y).subgroupOf Bs)
    (hxBs : x ∈ Bs) :
    sl6FixedMultiplicity (GaloisField 2 2) (rho ⟨x, hxBs⟩) = 4 := by
  classical
  obtain ⟨-, hxnot, -, -, -, -⟩ := ggF4N2_x_data hR hNbr
  have hane : rho ⟨x, hxBs⟩ ≠ 1 := by
    intro ha1
    have hxker : (⟨x, hxBs⟩ : Bs) ∈ rho.ker := MonoidHom.mem_ker.mpr ha1
    rw [hRhoKer] at hxker
    exact hxnot (Subgroup.mem_subgroupOf.mp hxker)
  have haord : orderOf (rho ⟨x, hxBs⟩) = 5 :=
    orderOf_eq_prime (hPow ⟨x, hxBs⟩) hane
  obtain ⟨-, ⟨F₀, hField, hFinite, hChar, hF₀, ⟨eJ⟩⟩, -⟩ :=
    ggF4N2J_original_mixed_recognition hR hNbr hL hK
  letI : Field F₀ := hField
  letI : Finite F₀ := hFinite
  letI : CharP F₀ 2 := hChar
  have hJK : J ≤ K := ggF4N2J_le_psl6_neighbor hR hNbr hL hK
  exact ggF4N2K_fixedMultiplicity_of_actualSL4_component
    (by simpa using GaloisField.card 2 2 (by norm_num)) hF₀ ψ hψ hker haord
    (ggF4N2J_isComponentOf_actual_lift_centralizer hR hNbr hL hK ψ rho hPoint hxBs)
    ((Subgroup.subgroupOfEquivOfLe hJK).trans eJ)

theorem ggF4N2J_fixedBlockRange_of_actual_lift
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G}
    {Rd Ra : Prop} (hR : GGSecFiveRestGen 5 B Bs x L D J Rd Ra)
    (hNbr : GGNbr 5 B x D J y K)
    (hL : GGCentralImage .POmegaMinus 4 2 L)
    (hK : GGCentralImage .PSL 6 2 K)
    (ψ : Matrix.SpecialLinearGroup (Fin 6) (GaloisField 2 2) →* K)
    (rho : Bs →* Matrix.SpecialLinearGroup (Fin 6) (GaloisField 2 2))
    (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin 6) (GaloisField 2 2)))
    (hPoint : ∀ (b : Bs) (k : K), ψ (rho b) * k * (ψ (rho b))⁻¹ =
      (K.normalizerMonoidHom.comp
        (Subgroup.inclusion (ggF4N2_Bs_le_normalizer_K hR hNbr hL))) b k)
    (hPow : ∀ b : Bs, (rho b) ^ 5 = 1)
    (hRhoKer : rho.ker = (Subgroup.zpowers y).subgroupOf Bs)
    (hxBs : x ∈ Bs) :
    J.subgroupOf K =
      ((CFSG.RankThree.CALinearPrimary.linearSpecialBlock
        (CFSG.RankThree.CALinearPrimary.slGL 6 (GaloisField 2 2) (rho ⟨x, hxBs⟩))
        (Polynomial.X - 1)).comap
          (CFSG.RankThree.CALinearPrimary.slGL 6 (GaloisField 2 2))).map ψ := by
  classical
  obtain ⟨-, hxnot, -, -, -, -⟩ := ggF4N2_x_data hR hNbr
  have hane : rho ⟨x, hxBs⟩ ≠ 1 := by
    intro ha1
    have hxker : (⟨x, hxBs⟩ : Bs) ∈ rho.ker := MonoidHom.mem_ker.mpr ha1
    rw [hRhoKer] at hxker
    exact hxnot (Subgroup.mem_subgroupOf.mp hxker)
  have haord : orderOf (rho ⟨x, hxBs⟩) = 5 :=
    orderOf_eq_prime (hPow ⟨x, hxBs⟩) hane
  obtain ⟨-, ⟨F₀, hField, hFinite, hChar, hF₀, ⟨eJ⟩⟩, -⟩ :=
    ggF4N2J_original_mixed_recognition hR hNbr hL hK
  letI : Field F₀ := hField
  letI : Finite F₀ := hFinite
  letI : CharP F₀ 2 := hChar
  have hJK : J ≤ K := ggF4N2J_le_psl6_neighbor hR hNbr hL hK
  exact ggF4N2K_fixedBlockRange_of_actualSL4_component
    (by simpa using GaloisField.card 2 2 (by norm_num)) hF₀ ψ hψ hker haord
    (ggF4N2J_isComponentOf_actual_lift_centralizer hR hNbr hL hK ψ rho hPoint hxBs)
    ((Subgroup.subgroupOfEquivOfLe hJK).trans eJ)

theorem ggF4N2J_layer_K_inf_centralizer_x
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    {Rd Ra : Prop} (hR : GGSecFiveRestGen 5 B Bs x L D J Rd Ra)
    (hNbr : GGNbr 5 B x D J y K)
    (hL : GGCentralImage .POmegaMinus 4 2 L)
    (hK : GGCentralImage .PSL 6 2 K) :
    LargeEvenLayer (K ⊓ Subgroup.centralizer ({x} : Set G)) = J := by
  classical
  obtain ⟨ψ, rho, hψ, hker, -, hPoint, hPow, hRhoKer, -, -, -⟩ :=
    ggF4N2_exists_actual_lift_sylow hR hNbr hL hK
  obtain ⟨hxBs, hxnot, -, -, -, -⟩ := ggF4N2_x_data hR hNbr
  let a := rho ⟨x, hxBs⟩
  have hane : a ≠ 1 := by
    intro ha1
    have hxker : (⟨x, hxBs⟩ : Bs) ∈ rho.ker := MonoidHom.mem_ker.mpr ha1
    rw [hRhoKer] at hxker
    exact hxnot (Subgroup.mem_subgroupOf.mp hxker)
  have ha : orderOf a = 5 := orderOf_eq_prime (hPow ⟨x, hxBs⟩) hane
  have hsf : sl6FixedMultiplicity (GaloisField 2 2) a = 4 :=
    ggF4N2J_fixedMultiplicity_of_actual_lift hR hNbr hL hK ψ rho hψ hker
      hPoint hPow hRhoKer hxBs
  let action : Bs →* MulAut K := K.normalizerMonoidHom.comp
    (Subgroup.inclusion (ggF4N2_Bs_le_normalizer_K hR hNbr hL))
  have hxact : ∀ k : K, ((action ⟨x, hxBs⟩ k : K) : G) =
      x * (k : G) * x⁻¹ := by
    have hact : action = CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.actK
        (ggF4N2_Bs_le_normalizer_K hR hNbr hL) := rfl
    intro k
    rw [hact]
    exact CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.coe_actK
      (ggF4N2_Bs_le_normalizer_K hR hNbr hL) ⟨x, hxBs⟩ k
  have hcent : (K ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf K =
      Subgroup.centralizer ({ψ a} : Set K) :=
    subgroupOf_inf_centralizer_eq_centralizer (action ⟨x, hxBs⟩)
      (fun k => hPoint ⟨x, hxBs⟩ k) hxact
  have hF : Nat.card (GaloisField 2 2) = 4 := by
    simpa using GaloisField.card 2 2 (by norm_num)
  have hJcomp := ggF4N2J_isComponentOf_actual_lift_centralizer
    hR hNbr hL hK ψ rho hPoint hxBs
  have hJeq := ggF4N2K_component_eq_fixedBlock_of_fixedMultiplicity
    hF ψ hψ hker ha hsf hJcomp
  have hJK := ggF4N2J_le_psl6_neighbor hR hNbr hL hK
  change sSup {M : Subgroup G | CFSG.Assembly.IsComponentOf M
    (K ⊓ Subgroup.centralizer ({x} : Set G))} = J
  apply le_antisymm
  · refine sSup_le ?_
    intro M hM
    have hMK : M ≤ K := hM.1.trans inf_le_left
    have hMcomp : CFSG.Assembly.IsComponentOf (M.subgroupOf K)
        (Subgroup.centralizer ({ψ a} : Set K)) := by
      have h := CFSG.LocalAnalysis.GLTheoremA.S265.isComponentOf_subgroupOf inf_le_left
        (CFSG.Assembly.isComponentOf_iff_open.mp hM)
      have h' := CFSG.Assembly.isComponentOf_iff_open.mpr h
      simpa only [hcent] using h'
    have hMeq : M.subgroupOf K = J.subgroupOf K :=
      (ggF4N2K_component_eq_fixedBlock_of_fixedMultiplicity
        hF ψ hψ hker ha hsf hMcomp).trans hJeq.symm
    have hmap := congrArg (Subgroup.map K.subtype) hMeq
    rw [Subgroup.map_subgroupOf_eq_of_le hMK, Subgroup.map_subgroupOf_eq_of_le hJK] at hmap
    exact le_of_eq hmap
  · exact le_sSup (ggF4N2J_isComponentOf_K_inf_centralizer_x hR hNbr hL hK)

theorem ggF4N2K_axis_plane_packet
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    {Rd Ra : Prop} (hR : GGSecFiveRestGen 5 B Bs x L D J Rd Ra)
    (hNbr : GGNbr 5 B x D J y K)
    (hL : GGCentralImage .POmegaMinus 4 2 L)
    (hK : GGCentralImage .PSL 6 2 K) :
    ∃ v : G,
      (
      v ∈ (D : Subgroup G) ⊓ K ∧
      orderOf v = 5 ∧
      D = Subgroup.zpowers y ⊔ Subgroup.zpowers v ∧
      Bs = Subgroup.zpowers y ⊔ (Bs ⊓ K) ∧
      Disjoint (Subgroup.zpowers y) K ∧
      CFSG.Assembly.IsComponentOf J (K ⊓ Subgroup.centralizer ({v} : Set G)) ∧
      LargeEvenLayer (K ⊓ Subgroup.centralizer ({v} : Set G)) = J ∧
      K ⊓ Subgroup.centralizer ({x} : Set G) = K ⊓ Subgroup.centralizer ({v} : Set G)
      ) ∧
      ∃ (ψ : Matrix.SpecialLinearGroup (Fin 6) (GaloisField 2 2) →* K)
        (rho : Bs →* Matrix.SpecialLinearGroup (Fin 6) (GaloisField 2 2)),
        Function.Surjective ψ ∧
        ψ.ker ≤ Subgroup.center
          (Matrix.SpecialLinearGroup (Fin 6) (GaloisField 2 2)) ∧
        (∀ b : Bs, MulAut.conj (ψ (rho b)) =
          (K.normalizerMonoidHom.comp
            (Subgroup.inclusion (ggF4N2_Bs_le_normalizer_K hR hNbr hL))) b) ∧
        (∀ (b : Bs) (k : K),
          ψ (rho b) * k * (ψ (rho b))⁻¹ =
            (K.normalizerMonoidHom.comp
              (Subgroup.inclusion (ggF4N2_Bs_le_normalizer_K hR hNbr hL))) b k) ∧
        (∀ b : Bs, (rho b) ^ 5 = 1) ∧
        rho.ker = (Subgroup.zpowers y).subgroupOf Bs ∧
        Nat.card rho.range = 5 ^ 3 ∧
        (K.subtype.comp (ψ.comp rho)).range = Bs ⊓ K ∧
        (∃ Q : Sylow 5
            (Matrix.SpecialLinearGroup (Fin 6) (GaloisField 2 2)),
          (Q : Subgroup
            (Matrix.SpecialLinearGroup (Fin 6) (GaloisField 2 2))) = rho.range) ∧
        v = (ψ (rho ⟨x, (ggF4N2_x_data hR hNbr).1⟩) : G) := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨ψ, rho, hSurj, hKer, hConj, hPoint, hPow, hRhoKer, hRhoCard, hRange,
    Q, hQ⟩ := ggF4N2_exists_actual_lift_sylow hR hNbr hL hK
  obtain ⟨hBsSplit, hDisj, _hCardK, _ψ', _rho', _hSurj', _hKer', _hConj', _hPoint',
    _hPow', _hRhoKer', _hRhoCard', _hRange'⟩ :=
    ggF4N2_exists_actual_torus_data hR hNbr hL hK
  obtain ⟨hxBs, hxNot, _hyOrder, hDclosure, _hDcard, _hDElem⟩ :=
    ggF4N2_x_data hR hNbr
  have hcfg : GGConfig 5 B Bs x L D J := hR.1
  have hpre : LargeEvenStdSubPre 5 B x L D J := hcfg.2.2.1
  let hBsN := ggF4N2_Bs_le_normalizer_K hR hNbr hL
  let action : Bs →* MulAut K :=
    K.normalizerMonoidHom.comp (Subgroup.inclusion hBsN)
  obtain ⟨_hActionKer, _hActionRange, _hActionPow, hActionNe⟩ :=
    ggF4N2_Bs_action_data hR hNbr hL hBsN
  let xB : Bs := ⟨x, hxBs⟩
  let vK : K := ψ (rho xB)
  let v : G := (vK : G)
  have hv5 : vK ^ 5 = 1 := by
    change (ψ (rho xB)) ^ 5 = 1
    rw [← map_pow, hPow xB, map_one]
  have hvNe : vK ≠ 1 := by
    intro hv
    have h := hConj xB
    change MulAut.conj vK = action xB at h
    rw [hv, map_one] at h
    exact hActionNe xB hxNot h.symm
  have hvOrder : orderOf vK = 5 := orderOf_eq_prime hv5 hvNe
  have hvpoint : ∀ k : K, x * (k : G) * x⁻¹ =
      (vK : G) * (k : G) * (vK : G)⁻¹ := by
    intro k
    have hp := hPoint xB k
    have hact : ((action xB k : K) : G) = x * (k : G) * x⁻¹ := by
      have hactdef : action =
          CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.actK hBsN := rfl
      rw [hactdef]
      exact CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.coe_actK hBsN xB k
    calc
      x * (k : G) * x⁻¹ = ((action xB k : K) : G) := hact.symm
      _ = (vK : G) * (k : G) * (vK : G)⁻¹ := congrArg Subtype.val hp.symm
  have hvBs : (vK : G) ∈ Bs := by
    have hvRange : (vK : G) ∈ (K.subtype.comp (ψ.comp rho)).range := ⟨xB, rfl⟩
    rw [hRange] at hvRange
    exact hvRange.1
  have hJcomp := ggF4N2J_isComponentOf_K_inf_centralizer_x hR hNbr hL hK
  have hJx : J ≤ K := hJcomp.1.trans inf_le_left
  have hJcx : J ≤ Subgroup.centralizer ({x} : Set G) := hJcomp.1.trans inf_le_right
  have hvCJ : (vK : G) ∈ Subgroup.centralizer (J : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    have hxj := Subgroup.mem_centralizer_singleton_iff.mp (hJcx hj)
    have hfixX : x * j * x⁻¹ = j := by
      rw [hxj.symm]
      group
    have hfixV := (hvpoint ⟨j, hJx hj⟩).symm.trans hfixX
    exact (mul_inv_eq_iff_eq_mul.mp hfixV).symm
  have hvD : v ∈ D := by
    rw [hpre.2.2.2.2.2.2, ggF4N2_B_eq_Bs hR hL]
    exact ⟨hvBs, hvCJ⟩
  have hYC : Subgroup.zpowers y ≤ Subgroup.centralizer (K : Set G) := by
    rw [← inf_centralizer_eq_zpowers_of_sHat hNbr.1]
    exact inf_le_right
  have hvNot : v ∉ Subgroup.zpowers y := by
    intro hvY
    have hvZ : vK ∈ Subgroup.center K := by
      rw [Subgroup.mem_center_iff]
      intro k
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hYC hvY) k k.2)
    have hAone : MulAut.conj vK = 1 := by
      apply DFunLike.ext
      intro k
      change vK * k * vK⁻¹ = k
      rw [← Subgroup.mem_center_iff.mp hvZ k]
      group
    exact hActionNe xB hxNot ((hConj xB).symm.trans hAone)
  have hyD : y ∈ D := by
    rw [hDclosure]
    exact Subgroup.subset_closure (by simp)
  have hvDspan : D = Subgroup.zpowers y ⊔ Subgroup.zpowers v := by
    simpa [v] using eq_sup_zpowers_of_card Nat.prime_five hpre.2.1 hpre.2.2.1
      hyD hNbr.1.2.2.1 hvD hvNot
  have hvCeq : K ⊓ Subgroup.centralizer ({x} : Set G) =
      K ⊓ Subgroup.centralizer ({v} : Set G) := by
    ext k
    constructor
    · rintro ⟨hkK, hkx⟩
      refine ⟨hkK, ?_⟩
      change k ∈ Subgroup.centralizer ({v} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hkx' : k ∈ Subgroup.centralizer ({x} : Set G) := hkx
      rw [Subgroup.mem_centralizer_singleton_iff] at hkx'
      have hxconj : x * (k : G) * x⁻¹ = (k : G) := by
        rw [hkx'.symm]
        group
      have hvconj : (v : G) * (k : G) * (v : G)⁻¹ = (k : G) :=
        (hvpoint ⟨k, hkK⟩).symm.trans hxconj
      exact (mul_inv_eq_iff_eq_mul.mp hvconj).symm
    · rintro ⟨hkK, hkv⟩
      refine ⟨hkK, ?_⟩
      change k ∈ Subgroup.centralizer ({x} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hkv' : k ∈ Subgroup.centralizer ({v} : Set G) := hkv
      rw [Subgroup.mem_centralizer_singleton_iff] at hkv'
      have hvconj : (v : G) * (k : G) * (v : G)⁻¹ = (k : G) := by
        rw [hkv'.symm]
        group
      have hxconj : x * (k : G) * x⁻¹ = (k : G) :=
        (hvpoint ⟨k, hkK⟩).trans hvconj
      exact (mul_inv_eq_iff_eq_mul.mp hxconj).symm
  have hcomp : CFSG.Assembly.IsComponentOf J
      (K ⊓ Subgroup.centralizer ({v} : Set G)) := by
    rw [← hvCeq]
    exact ggF4N2J_isComponentOf_K_inf_centralizer_x hR hNbr hL hK
  have hLayer : LargeEvenLayer (K ⊓ Subgroup.centralizer ({v} : Set G)) = J := by
    rw [← hvCeq]
    exact ggF4N2J_layer_K_inf_centralizer_x hR hNbr hL hK
  refine ⟨v, ?_, ψ, rho, hSurj, hKer, hConj, hPoint, hPow, hRhoKer, hRhoCard, hRange,
    ⟨Q, hQ⟩, ?_⟩
  · exact ⟨⟨hvD, vK.2⟩, by simpa [v] using hvOrder, hvDspan, hBsSplit, hDisj, hcomp, hLayer, hvCeq⟩
  · rfl

theorem ggF4N2K_axis_plane
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    {Rd Ra : Prop} (hR : GGSecFiveRestGen 5 B Bs x L D J Rd Ra)
    (hNbr : GGNbr 5 B x D J y K)
    (hL : GGCentralImage .POmegaMinus 4 2 L)
    (hK : GGCentralImage .PSL 6 2 K) :
    ∃ v : G,
      v ∈ (D : Subgroup G) ⊓ K ∧
      orderOf v = 5 ∧
      D = Subgroup.zpowers y ⊔ Subgroup.zpowers v ∧
      Bs = Subgroup.zpowers y ⊔ (Bs ⊓ K) ∧
      Disjoint (Subgroup.zpowers y) K ∧
      CFSG.Assembly.IsComponentOf J (K ⊓ Subgroup.centralizer ({v} : Set G)) ∧
      LargeEvenLayer (K ⊓ Subgroup.centralizer ({v} : Set G)) = J ∧
      K ⊓ Subgroup.centralizer ({x} : Set G) = K ⊓ Subgroup.centralizer ({v} : Set G) := by
  obtain ⟨v, hbody⟩ := ggF4N2K_axis_plane_packet hR hNbr hL hK
  exact ⟨v, hbody.1⟩


private lemma out5Inner_sl_four_of_card {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 4) :
    CFSG.Quasithin.SBc17.Out5Inner (Matrix.SpecialLinearGroup (Fin 4) F) := by
  classical
  have hcard : Nat.card
      (CFSG.ComponentClassification.OuterAutomorphisms.Outer
        (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 4 F)) ≤ 4 :=
    Nat.le_of_dvd (by norm_num : 0 < 4)
      (CFSG.OddStandard.AltStdSec.card_outer_dvd_four hF)
  have hOutP : CFSG.Quasithin.SBc17.Out5Inner
      (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 4 F) :=
    CFSG.Quasithin.SBc17.out5Inner_of_card_outer_le_four hcard
  exact CFSG.Quasithin.SBc17.Out5Inner.of_mulEquiv
    (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSLFourEquivSL F) hOutP


theorem ggF4N2_D_eq_Bs_inf_centralizer_J
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {Rd Ra : Prop} (hR : GGSecFiveRestGen 5 B Bs x L D J Rd Ra)
    (hL : GGCentralImage .POmegaMinus 4 2 L) :
    D = Bs ⊓ Subgroup.centralizer (J : Set G) := by
  have hD : D = B ⊓ Subgroup.centralizer (J : Set G) :=
    hR.1.2.2.1.2.2.2.2.2.2
  simpa [ggF4N2_B_eq_Bs hR hL] using hD


private theorem ggF4N2J_original_torus_split_core
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    {Rd Ra : Prop} (hR : GGSecFiveRestGen 5 B Bs x L D J Rd Ra)
    (hNbr : GGNbr 5 B x D J y K)
    (hL : GGCentralImage .POmegaMinus 4 2 L)
    (hK : GGCentralImage .PSL 6 2 K) :
    (Bs : Subgroup G) = (D : Subgroup G) ⊔ (Bs ⊓ J) ∧
      Disjoint (D : Subgroup G) (J : Subgroup G) ∧ Nat.card ↥(Bs ⊓ J) = 25 := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hrank := ggF4N2Rank hR hL
  have hcardBs : Nat.card Bs = 5 ^ 4 := hrank.1
  have hcardB : Nat.card B = 5 ^ 4 := hrank.2.1
  have hBsB : B ≤ Bs := hR.1.2.1.1
  have hBeq : B = Bs :=
    Subgroup.eq_of_le_of_card_ge hBsB (by rw [hcardBs, hcardB])
  have hDJ : LargeEvenStdSubPre 5 B x L D J := hR.1.2.2.1
  have hD_le_B : D ≤ B := hDJ.1
  have hDcard : Nat.card D = 25 := by
    rw [hDJ.2.2.1]
    norm_num
  have hDeq : D = Bs ⊓ Subgroup.centralizer (J : Set G) :=
    ggF4N2_D_eq_Bs_inf_centralizer_J hR hL
  have hD_le_Bs : D ≤ Bs := by
    rw [hDeq]
    exact inf_le_left
  have hcfg : GGConfig 5 B Bs x L D J := hR.1
  have hBsBstar : GGBstar 5 B Bs := hcfg.2.1
  have hcommBs : ∀ a ∈ Bs, ∀ b ∈ Bs, a * b = b * a :=
    fun a ha b hb =>
      congrArg Subtype.val (hBsBstar.2.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hBsJ : Bs ≤ Subgroup.normalizer (J : Set G) := ggF4N2J_Bs_le_normalizer hR
  obtain ⟨_, ⟨F, hFfield, hFfinite, hFchar, hFcard, eJne⟩, _⟩ :=
    ggF4N2J_original_mixed_recognition hR hNbr hL hK
  letI : Field F := hFfield
  letI : Finite F := hFfinite
  letI : CharP F 2 := hFchar
  obtain ⟨eJ⟩ := eJne
  have hcenterJ : Subgroup.center J = ⊥ :=
    CFSG.GorensteinWalter.center_eq_bot_of_mulEquiv eJ
      (CFSG.EvenSmallLie.UnitarySix.YamadaInputs.center_SL_four_eq_bot hFcard)
  have hDdisjJ : Disjoint D J := by
    rw [disjoint_iff]
    apply le_bot_iff.mp
    intro z hz
    rw [Subgroup.mem_bot]
    have hzD : z ∈ D := hz.1
    have hzJ : z ∈ J := hz.2
    have hzC : z ∈ Subgroup.centralizer (J : Set G) := by
      rw [hDeq] at hzD
      exact hzD.2
    have hzcenter : (⟨z, hzJ⟩ : J) ∈ Subgroup.center J := by
      rw [Subgroup.mem_center_iff]
      intro w
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.mp hzC (w : J) w.2
    have hzone : (⟨z, hzJ⟩ : J) = 1 := by
      simpa [hcenterJ] using hzcenter
    exact Subtype.ext_iff.mp hzone
  have hOut5J : CFSG.Quasithin.SBc17.Out5Inner J :=
    (out5Inner_sl_four_of_card hFcard).of_mulEquiv eJ.symm
  have hAutJ : ∀ σ : MulAut J, σ ^ 5 = 1 → ∃ a : J, σ = MulAut.conj a := by
    intro σ hσ
    obtain ⟨a, ha⟩ := hOut5J σ hσ
    refine ⟨a, MulEquiv.ext ?_⟩
    intro z
    simpa [MulAut.conj_apply] using ha z
  have hcenterJ' : ∀ z : J, (∀ w : J, z * w = w * z) → z = 1 := by
    intro z hz
    have hzc : z ∈ Subgroup.center J := Subgroup.mem_center_iff.mpr (fun w => (hz w).symm)
    simpa [hcenterJ] using hzc
  let β : Bs →* MulAut J :=
    Subgroup.normalizerMonoidHom (H := J).comp (Subgroup.inclusion hBsJ)
  have hBsPow : ∀ b : Bs, b ^ 5 = 1 := by
    intro b
    apply Subtype.ext
    exact hR.1.2.1.2.1.2 (b : G) b.2
  obtain ⟨rhoJ, hrho_apply⟩ :=
    CFSG.LocalAnalysis.GLTheoremB.MovingAround.OmegaFacts2.exists_inner_hom
      (p := 5) (D := Bs) hBsPow (MulEquiv.refl J) β hAutJ hcenterJ'
  have hβapply : ∀ (b : Bs) (z : J), (β b z : G) = (b : G) * (z : G) * (b : G)⁻¹ := by
    intro b z
    change ((Subgroup.normalizerMonoidHom (H := J)) (Subgroup.inclusion hBsJ b) z : G) =
      (b : G) * (z : G) * (b : G)⁻¹
    rfl
  have hrhoAut : ∀ b : Bs, MulAut.conj (rhoJ b) = β b := by
    intro b
    apply MulEquiv.ext
    intro z
    simpa using (hrho_apply b z).symm
  have hrhoPow : ∀ b : Bs, (rhoJ b) ^ 5 = 1 := by
    intro b
    have hβpow : β b ^ 5 = 1 := by
      rw [← map_pow, hBsPow b, map_one]
    have hconjpow : MulAut.conj ((rhoJ b) ^ 5) = 1 := by
      rw [map_pow, hrhoAut b, hβpow]
    have hcentral : (rhoJ b) ^ 5 ∈ Subgroup.center J := by
      rw [Subgroup.mem_center_iff]
      intro z
      have hz := congrArg (fun f : MulAut J => f z) hconjpow
      simp only [MulAut.conj_apply, MulAut.one_apply] at hz
      have hz' : (rhoJ b) ^ 5 * z = z * (rhoJ b) ^ 5 := by
        have := congrArg (fun w : J => w * (rhoJ b) ^ 5) hz
        simpa [mul_assoc] using this
      exact hz'.symm
    simpa [hcenterJ] using hcentral
  have hrhoCentral : ∀ b : Bs,
      (rhoJ b : G) ∈ Subgroup.centralizer (Bs : Set G) := by
    intro b
    rw [Subgroup.mem_centralizer_iff]
    intro b' hb'
    let aN : Subgroup.normalizer (J : Set G) := ⟨(rhoJ b : G), Subgroup.le_normalizer (rhoJ b).2⟩
    let bN : Subgroup.normalizer (J : Set G) := ⟨b', hBsJ hb'⟩
    let cN : Subgroup.normalizer (J : Set G) := aN * bN * aN⁻¹ * bN⁻¹
    have hcommAut : β b * β ⟨b', hb'⟩ = β ⟨b', hb'⟩ * β b := by
      calc
        β b * β ⟨b', hb'⟩ = β (b * ⟨b', hb'⟩) := (map_mul β b ⟨b', hb'⟩).symm
        _ = β (⟨b', hb'⟩ * b) := by
          congr 1
          apply Subtype.ext
          exact hcommBs (b : G) b.2 b' hb'
        _ = β ⟨b', hb'⟩ * β b := map_mul β ⟨b', hb'⟩ b
    have hφa : Subgroup.normalizerMonoidHom (H := J) aN = β b := by
      apply MulEquiv.ext
      intro z
      apply Subtype.ext
      have hz := congrArg (fun f : MulAut J => f z) (hrhoAut b)
      simpa [MulAut.conj_apply] using congrArg (fun w : J => (w : G)) hz
    have hφb : Subgroup.normalizerMonoidHom (H := J) bN = β ⟨b', hb'⟩ := by
      apply MulEquiv.ext
      intro z
      apply Subtype.ext
      rw [hβapply]
      rfl
    have hker : cN ∈ Subgroup.normalizerMonoidHom (H := J).ker := by
      rw [MonoidHom.mem_ker]
      change Subgroup.normalizerMonoidHom (H := J) (aN * bN * aN⁻¹ * bN⁻¹) = 1
      simp only [map_mul, map_inv]
      rw [hφa, hφb, hcommAut]
      group
    have hcC : (cN : G) ∈ Subgroup.centralizer (J : Set G) := by
      rw [Subgroup.normalizerMonoidHom_ker] at hker
      exact Subgroup.mem_subgroupOf.mp hker
    have hcJ : (cN : G) ∈ J := by
      change (rhoJ b : G) * b' * (rhoJ b : G)⁻¹ * b'⁻¹ ∈ J
      have hconj : b' * (rhoJ b : G)⁻¹ * b'⁻¹ ∈ J := by
        exact (Subgroup.mem_normalizer_iff.mp (hBsJ hb') ((rhoJ b : G)⁻¹)).mp
          (J.inv_mem (rhoJ b).2)
      rw [show (rhoJ b : G) * b' * (rhoJ b : G)⁻¹ * b'⁻¹ =
          (rhoJ b : G) * (b' * (rhoJ b : G)⁻¹ * b'⁻¹) by group]
      exact J.mul_mem (rhoJ b).2 hconj
    have hcCenter : (⟨(cN : G), hcJ⟩ : J) ∈ Subgroup.center J := by
      rw [Subgroup.mem_center_iff]
      intro w
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.mp hcC (w : J) w.2
    have hcJone : (⟨(cN : G), hcJ⟩ : J) = 1 := by
      simpa [hcenterJ] using hcCenter
    have hcOne : (cN : G) = 1 := Subtype.ext_iff.mp hcJone
    have hcOne' : (rhoJ b : G) * b' * (rhoJ b : G)⁻¹ * b'⁻¹ = 1 := hcOne
    have hcomm : (rhoJ b : G) * b' = b' * (rhoJ b : G) := by
      calc
        (rhoJ b : G) * b' = ((rhoJ b : G) * b' * (rhoJ b : G)⁻¹ * b'⁻¹) *
            (b' * (rhoJ b : G)) := by group
        _ = 1 * (b' * (rhoJ b : G)) := by rw [hcOne']
        _ = b' * (rhoJ b : G) := by simp
    exact hcomm.symm
  have hrhoMem : ∀ b : Bs, (rhoJ b : G) ∈ Bs := by
    intro b
    obtain ⟨P, hP⟩ := ggF4N2_actual_intersection_isSylow hR hNbr hL hK
    let rhoK : K := ⟨(rhoJ b : G), ggF4N2J_le_psl6_neighbor hR hNbr hL hK (rhoJ b).2⟩
    have hrhoKpow : rhoK ^ 5 = 1 := by
      apply Subtype.ext
      exact congrArg (fun z : J => (z : G)) (hrhoPow b)
    have hPKcent : (P : Subgroup K) ≤ Subgroup.centralizer ({rhoK} : Set K) := by
      intro z hz
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply Subtype.ext
      have hzBs : (z : G) ∈ Bs := by
        rw [hP] at hz
        exact (Subgroup.mem_subgroupOf.mp hz).1
      exact Subgroup.mem_centralizer_iff.mp (hrhoCentral b) (z : G) hzBs
    have hrhoP : rhoK ∈ (P : Subgroup K) :=
      CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.spw_mem_of_centralizes
        P hrhoKpow hPKcent
    rw [hP] at hrhoP
    exact (Subgroup.mem_subgroupOf.mp hrhoP).1
  have hdiff : ∀ b : Bs, (b : G) * (rhoJ b : G)⁻¹ ∈ D := by
    intro b
    have hmemBs : (b : G) * (rhoJ b : G)⁻¹ ∈ Bs :=
      Bs.mul_mem b.2 (Bs.inv_mem (hrhoMem b))
    have hsame : ∀ y : J,
        (b : G) * (y : G) * (b : G)⁻¹ =
          (rhoJ b : G) * (y : G) * (rhoJ b : G)⁻¹ := by
      intro y
      have hb := hβapply b y
      have hr : (β b y : G) = (rhoJ b : G) * (y : G) * (rhoJ b : G)⁻¹ := by
        have hz := congrArg (fun f : MulAut J => f y) (hrhoAut b)
        simpa [MulAut.conj_apply] using congrArg (fun w : J => (w : G)) hz.symm
      exact hb.trans hr
    have hcen : (b : G) * (rhoJ b : G)⁻¹ ∈ Subgroup.centralizer (J : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      let y : J := ⟨(rhoJ b : G)⁻¹ * z * (rhoJ b : G), by
        exact J.mul_mem (J.mul_mem (J.inv_mem (rhoJ b).2) hz) (rhoJ b).2⟩
      have hconj : ((b : G) * (rhoJ b : G)⁻¹) * z * ((b : G) * (rhoJ b : G)⁻¹)⁻¹ = z := by
        calc
          ((b : G) * (rhoJ b : G)⁻¹) * z * ((b : G) * (rhoJ b : G)⁻¹)⁻¹ =
              (b : G) * ((rhoJ b : G)⁻¹ * z * (rhoJ b : G)) * (b : G)⁻¹ := by group
          _ = (b : G) * (y : G) * (b : G)⁻¹ := rfl
          _ = (rhoJ b : G) * (y : G) * (rhoJ b : G)⁻¹ := hsame y
          _ = z := by simp [y]; group
      have hcz : ((b : G) * (rhoJ b : G)⁻¹) * z = z * ((b : G) * (rhoJ b : G)⁻¹) := by
        have := congrArg (fun w : G => w * ((b : G) * (rhoJ b : G)⁻¹)) hconj
        simpa [mul_assoc] using this
      exact hcz.symm
    rw [hDeq]
    exact ⟨hmemBs, hcen⟩
  have hsplit : Bs = D ⊔ (Bs ⊓ J) := by
    apply le_antisymm
    · intro b hb
      have hcD : (b : G) * (rhoJ ⟨b, hb⟩)⁻¹ ∈ D := hdiff ⟨b, hb⟩
      have hrho : (rhoJ ⟨b, hb⟩ : G) ∈ Bs ⊓ J :=
        ⟨hrhoMem ⟨b, hb⟩, (rhoJ ⟨b, hb⟩).2⟩
      have hprod : (b : G) * (rhoJ ⟨b, hb⟩ : G)⁻¹ * (rhoJ ⟨b, hb⟩ : G) = b := by group
      rw [← hprod]
      exact Subgroup.mul_mem_sup hcD hrho
    · exact sup_le hD_le_Bs inf_le_left
  have hDisj : Disjoint D J := hDdisjJ
  have hcardInt : Nat.card ↥(Bs ⊓ J) = 25 := by
    have hnorm : (Bs ⊓ J : Subgroup G) ≤
        Subgroup.normalizer (D : Set G) := by
      intro z hz
      rw [Subgroup.mem_normalizer_iff]
      intro d
      constructor
      · intro hd
        have hdBs : d ∈ Bs := hD_le_Bs hd
        have hcomm : z * d = d * z := hcommBs z hz.1 d hdBs
        rw [show z * d * z⁻¹ = d by rw [hcomm]; group]
        exact hd
      · intro hd
        have hzdBs : z * d * z⁻¹ ∈ Bs := hD_le_Bs hd
        have hdBs : d ∈ Bs := by
          rw [show d = z⁻¹ * (z * d * z⁻¹) * z by group]
          exact Bs.mul_mem (Bs.mul_mem (Bs.inv_mem hz.1) hzdBs) hz.1
        have hcomm : z * d = d * z := hcommBs z hz.1 d hdBs
        rw [hcomm] at hd
        simpa [mul_assoc] using hd
    have hDisj' : Disjoint D (Bs ⊓ J) := hDdisjJ.mono_right inf_le_right
    have hcardProd :=
      CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
        D (Bs ⊓ J) hnorm hDisj'
    have hcardSup : Nat.card ↥(D ⊔ (Bs ⊓ J)) = Nat.card Bs := by rw [← hsplit]
    have hmain : 25 * Nat.card ↥(Bs ⊓ J) = 25 * 25 := by
      calc
        25 * Nat.card ↥(Bs ⊓ J) = Nat.card D * Nat.card ↥(Bs ⊓ J) := by rw [hDcard]
        _ = Nat.card ↥(D ⊔ (Bs ⊓ J)) := hcardProd.symm
        _ = Nat.card Bs := hcardSup
        _ = 5 ^ 4 := hcardBs
        _ = 25 * 25 := by norm_num
    exact Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 25) hmain
  exact ⟨hsplit, hDisj, hcardInt⟩


private lemma not_five_cube_dvd_card_SL_four {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 4) :
    ¬ 5 ^ 3 ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 4) F) := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  have hq : Fintype.card F = 4 := by rwa [Nat.card_eq_fintype_card] at hF
  rw [Matrix.card_SL_field]
  simp only [Fin.prod_univ_four, hq]
  norm_num

theorem ggF4N2J_original_torus_split
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    {Rd Ra : Prop} (hR : GGSecFiveRestGen 5 B Bs x L D J Rd Ra)
    (hNbr : GGNbr 5 B x D J y K)
    (hL : GGCentralImage .POmegaMinus 4 2 L)
    (hK : GGCentralImage .PSL 6 2 K) :
    (Bs : Subgroup G) = (D : Subgroup G) ⊔ (Bs ⊓ J) ∧
      Disjoint (D : Subgroup G) (J : Subgroup G) ∧
      Nat.card ↥(Bs ⊓ J) = 25 ∧
      ∃ P : Sylow 5 J,
        (P : Subgroup J) = (Bs ⊓ J).subgroupOf J := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hcore := ggF4N2J_original_torus_split_core hR hNbr hL hK
  obtain ⟨hsplit, hdisj, hcardInt⟩ := hcore
  obtain ⟨_, ⟨F, hFfield, hFfinite, hFchar, hFcard, eJne⟩, _⟩ :=
    ggF4N2J_original_mixed_recognition hR hNbr hL hK
  letI : Field F := hFfield
  letI : Finite F := hFfinite
  letI : CharP F 2 := hFchar
  obtain ⟨eJ⟩ := eJne
  let H : Subgroup J := (Bs ⊓ J).subgroupOf J
  have hHcard : Nat.card H = 25 := by
    change Nat.card ↥((Bs ⊓ J).subgroupOf J) = 25
    rw [← hcardInt]
    exact Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (H := Bs ⊓ J) (K := J) inf_le_right).toEquiv
  have hHp : IsPGroup 5 H :=
    IsPGroup.of_card (p := 5) (n := 2) (by simpa using hHcard)
  have hnotJ : ¬ 5 ^ 3 ∣ Nat.card J := by
    rw [Nat.card_congr eJ.toEquiv]
    exact not_five_cube_dvd_card_SL_four hFcard
  have hHindex : ¬ 5 ∣ H.index := by
    intro h5
    apply hnotJ
    rw [← Subgroup.index_mul_card (H := H)]
    rw [show 5 ^ 3 = 5 * 5 ^ 2 by norm_num]
    exact mul_dvd_mul h5 (by rw [hHcard]; norm_num)
  let P : Sylow 5 J := hHp.toSylow hHindex
  refine ⟨hsplit, hdisj, hcardInt, P, ?_⟩
  simpa [P, H, IsPGroup.toSylow_coe]

end CFSG.StandardType

end


public section

namespace CFSG.StandardType.N2KCoordinate

open CFSG.Open CFSG.SeitzReduction.LinearPilot
open Polynomial Module
open CFSG.RankThree.PartOne.KCPrimary
open CFSG.RankThree.PartOne.KCOrthogonal

noncomputable section

set_option maxHeartbeats 4000000

theorem sl6End_fixedSubmodule_eq_primaryComponent
    {F : Type} [Field F] {a : Matrix.SpecialLinearGroup (Fin 6) F} :
    (sl6End F a).fixedSubmodule =
      primaryComponent (sl6End F a) (X - 1) := by
  ext v
  rw [LinearMap.mem_fixedSubmodule_iff, mem_primaryComponent]
  simp [sub_eq_zero]

theorem sl6FixedMultiplicity_eq_finrank_fixedSubmodule
    {F : Type} [Field F] [Finite F] [CharP F 2]
    {a : Matrix.SpecialLinearGroup (Fin 6) F} (ha : orderOf a = 5) :
    sl6FixedMultiplicity F a =
      Module.finrank F (sl6End F a).fixedSubmodule := by
  classical
  haveI : Fact (Irreducible (X - 1 : F[X])) :=
    ⟨CFSG.RankThree.Classical.irreducible_X_sub_one⟩
  have hdeg : (X - 1 : F[X]).natDegree = 1 := by
    simpa using (natDegree_X_sub_C (1 : F))
  by_cases hmem : (X - 1 : F[X]) ∈ primaryFactors (sl6End F a)
  · rw [sl6FixedMultiplicity_eq_of_fixed hmem rfl,
      sl6End_fixedSubmodule_eq_primaryComponent,
      finrank_primaryComponent (x := sl6End F a) (a := (X - 1 : F[X])),
      hdeg, one_mul]
  · have hsum : sl6FixedMultiplicity F a = 0 := by
      rw [sl6FixedMultiplicity]
      apply Finset.sum_eq_zero
      intro b hb
      have hbne : (b : F[X]) ≠ X - 1 := by
        intro h
        exact hmem (h ▸ b.2)
      simp [hbne]
    have hbot : primaryComponent (sl6End F a) (X - 1) = ⊥ :=
      CFSG.RankThree.Classical.primaryComponent_eq_bot_of_not_mem
        CFSG.RankThree.Classical.irreducible_X_sub_one
        CFSG.RankThree.Classical.monic_X_sub_one hmem
    rw [hsum, sl6End_fixedSubmodule_eq_primaryComponent, hbot, finrank_bot]


abbrev F4c : Type := CFSG.Fischer.F4

abbrev SL2F4c : Type := Matrix.SpecialLinearGroup (Fin 2) F4c

noncomputable def f4cEquiv : F4c ≃+* F4 :=
  CFSG.Fischer.F4.equivGaloisField

theorem sl2F4c_no_fixed_of_orderFive :
    ∀ (B : SL2F4c) (v : Fin 2 → F4c),
      B ^ 5 = 1 → B ≠ 1 →
        (B : Matrix (Fin 2) (Fin 2) F4c).mulVec v = v → v = 0 := by
  decide +kernel

theorem sl2F4_no_fixed_of_orderFive :
    ∀ (B : SL2F4) (v : Fin 2 → F4),
      B ^ 5 = 1 → B ≠ 1 →
        (B : Matrix (Fin 2) (Fin 2) F4).mulVec v = v → v = 0 := by
  intro B v hB5 hB1 hv
  classical
  let e := f4cEquiv
  let Bc : SL2F4c := Matrix.SpecialLinearGroup.map e.symm.toRingHom B
  let vc : Fin 2 → F4c := fun i => e.symm (v i)
  have hBc5 : Bc ^ 5 = 1 := by
    dsimp [Bc]
    rw [← map_pow, hB5, map_one]
  have hcomp :
      (Matrix.SpecialLinearGroup.map e.toRingHom)
        ((Matrix.SpecialLinearGroup.map e.symm.toRingHom) B) = B := by
    apply Subtype.ext
    change (((B : Matrix (Fin 2) (Fin 2) F4).map (⇑e.symm)).map (⇑e)) =
      (B : Matrix (Fin 2) (Fin 2) F4)
    rw [Matrix.map_map]
    ext i j
    simp
  have hBc1 : Bc ≠ 1 := by
    intro h
    apply hB1
    have h' := congrArg (Matrix.SpecialLinearGroup.map e.toRingHom) h
    rw [show (Matrix.SpecialLinearGroup.map e.toRingHom) Bc =
        (Matrix.SpecialLinearGroup.map e.toRingHom)
          ((Matrix.SpecialLinearGroup.map e.symm.toRingHom) B) from rfl] at h'
    rw [hcomp] at h'
    simpa using h'
  have hvc : (Bc : Matrix (Fin 2) (Fin 2) F4c).mulVec vc = vc := by
    funext i
    have hmap := RingHom.map_mulVec e.symm.toRingHom
      (B : Matrix (Fin 2) (Fin 2) F4) v i
    have h' : e.symm ((B : Matrix (Fin 2) (Fin 2) F4).mulVec v i) = vc i := by
      rw [hv]
    calc
      ((Bc : Matrix (Fin 2) (Fin 2) F4c).mulVec vc) i =
          (((B : Matrix (Fin 2) (Fin 2) F4).map e.symm).mulVec vc) i := by
        rfl
      _ = e.symm ((B : Matrix (Fin 2) (Fin 2) F4).mulVec v i) := hmap.symm
      _ = vc i := h'
  have hv0 : vc = 0 := sl2F4c_no_fixed_of_orderFive Bc vc hBc5 hBc1 hvc
  funext i
  have hi : vc i = 0 := congrFun hv0 i
  have := congrArg e hi
  simpa [vc] using this

abbrev TorusBlockV2 : Type := Fin 2 → F4
abbrev TorusBlockTriple : Type := TorusBlockV2 × (TorusBlockV2 × TorusBlockV2)

noncomputable def torusBlockIdx : Fin 6 ≃ Fin 2 ⊕ (Fin 2 ⊕ Fin 2) :=
  (finSumFinEquiv (m := 2) (n := 4)).symm |>.trans
    (Equiv.sumCongr (Equiv.refl (Fin 2))
      (finSumFinEquiv (m := 2) (n := 2)).symm)


@[simp] theorem torusFirstSymm0 :
    (finSumFinEquiv (m := 2) (n := 4)).symm (0 : Fin 6) = Sum.inl (0 : Fin 2) := by
  decide
@[simp] theorem torusFirstSymm1 :
    (finSumFinEquiv (m := 2) (n := 4)).symm (1 : Fin 6) = Sum.inl (1 : Fin 2) := by
  decide
@[simp] theorem torusFirstSymm2 :
    (finSumFinEquiv (m := 2) (n := 4)).symm (2 : Fin 6) = Sum.inr (0 : Fin 4) := by
  decide
@[simp] theorem torusFirstSymm3 :
    (finSumFinEquiv (m := 2) (n := 4)).symm (3 : Fin 6) = Sum.inr (1 : Fin 4) := by
  decide
@[simp] theorem torusFirstSymm4 :
    (finSumFinEquiv (m := 2) (n := 4)).symm (4 : Fin 6) = Sum.inr (2 : Fin 4) := by
  decide
@[simp] theorem torusFirstSymm5 :
    (finSumFinEquiv (m := 2) (n := 4)).symm (5 : Fin 6) = Sum.inr (3 : Fin 4) := by
  decide
@[simp] theorem torusFinSumInl0 :
    (finSumFinEquiv (m := 2) (n := 4)) (Sum.inl (0 : Fin 2)) = (0 : Fin 6) := by
  decide
@[simp] theorem torusFinSumInl1 :
    (finSumFinEquiv (m := 2) (n := 4)) (Sum.inl (1 : Fin 2)) = (1 : Fin 6) := by
  decide
@[simp] theorem torusFinSumInr0 :
    (finSumFinEquiv (m := 2) (n := 4)) (Sum.inr (0 : Fin 4)) = (2 : Fin 6) := by
  decide
@[simp] theorem torusFinSumInr1 :
    (finSumFinEquiv (m := 2) (n := 4)) (Sum.inr (1 : Fin 4)) = (3 : Fin 6) := by
  decide
@[simp] theorem torusFinSumInr2 :
    (finSumFinEquiv (m := 2) (n := 4)) (Sum.inr (2 : Fin 4)) = (4 : Fin 6) := by
  decide
@[simp] theorem torusFinSumInr3 :
    (finSumFinEquiv (m := 2) (n := 4)) (Sum.inr (3 : Fin 4)) = (5 : Fin 6) := by
  decide
@[simp] theorem torusFinSumSymm0 :
    (finSumFinEquiv (m := 2) (n := 2)).symm (0 : Fin 4) = Sum.inl (0 : Fin 2) := by
  decide
@[simp] theorem torusFinSumSymm1 :
    (finSumFinEquiv (m := 2) (n := 2)).symm (1 : Fin 4) = Sum.inl (1 : Fin 2) := by
  decide
@[simp] theorem torusFinSumSymm2 :
    (finSumFinEquiv (m := 2) (n := 2)).symm (2 : Fin 4) = Sum.inr (0 : Fin 2) := by
  decide
@[simp] theorem torusFinSumSymm3 :
    (finSumFinEquiv (m := 2) (n := 2)).symm (3 : Fin 4) = Sum.inr (1 : Fin 2) := by
  decide
@[simp] theorem torusFinSum2Inl0 :
    (finSumFinEquiv (m := 2) (n := 2)) (Sum.inl (0 : Fin 2)) = (0 : Fin 4) := by
  decide
@[simp] theorem torusFinSum2Inl1 :
    (finSumFinEquiv (m := 2) (n := 2)) (Sum.inl (1 : Fin 2)) = (1 : Fin 4) := by
  decide
@[simp] theorem torusFinSum2Inr0 :
    (finSumFinEquiv (m := 2) (n := 2)) (Sum.inr (0 : Fin 2)) = (2 : Fin 4) := by
  decide
@[simp] theorem torusFinSum2Inr1 :
    (finSumFinEquiv (m := 2) (n := 2)) (Sum.inr (1 : Fin 2)) = (3 : Fin 4) := by
  decide

@[simp] theorem torusBlockIdx_zero : torusBlockIdx (0 : Fin 6) = Sum.inl (0 : Fin 2) := by
  decide
@[simp] theorem torusBlockIdx_one : torusBlockIdx (1 : Fin 6) = Sum.inl (1 : Fin 2) := by
  decide
@[simp] theorem torusBlockIdx_two : torusBlockIdx (2 : Fin 6) = Sum.inr (Sum.inl (0 : Fin 2)) := by
  decide
@[simp] theorem torusBlockIdx_three : torusBlockIdx (3 : Fin 6) = Sum.inr (Sum.inl (1 : Fin 2)) := by
  decide
@[simp] theorem torusBlockIdx_four : torusBlockIdx (4 : Fin 6) = Sum.inr (Sum.inr (0 : Fin 2)) := by
  decide
@[simp] theorem torusBlockIdx_five : torusBlockIdx (5 : Fin 6) = Sum.inr (Sum.inr (1 : Fin 2)) := by
  decide
@[simp] theorem torusBlockIdx_symm_zero : torusBlockIdx.symm (Sum.inl (0 : Fin 2)) = (0 : Fin 6) := by
  decide
@[simp] theorem torusBlockIdx_symm_one : torusBlockIdx.symm (Sum.inl (1 : Fin 2)) = (1 : Fin 6) := by
  decide
@[simp] theorem torusBlockIdx_symm_two : torusBlockIdx.symm (Sum.inr (Sum.inl (0 : Fin 2))) = (2 : Fin 6) := by
  decide
@[simp] theorem torusBlockIdx_symm_three : torusBlockIdx.symm (Sum.inr (Sum.inl (1 : Fin 2))) = (3 : Fin 6) := by
  decide
@[simp] theorem torusBlockIdx_symm_four : torusBlockIdx.symm (Sum.inr (Sum.inr (0 : Fin 2))) = (4 : Fin 6) := by
  decide
@[simp] theorem torusBlockIdx_symm_five : torusBlockIdx.symm (Sum.inr (Sum.inr (1 : Fin 2))) = (5 : Fin 6) := by
  decide

noncomputable def torusBlockEquiv :
    (Fin 6 → F4) ≃ₗ[F4] TorusBlockTriple :=
  (LinearEquiv.piCongrLeft F4 (fun _ => F4) torusBlockIdx).trans <|
    (LinearEquiv.sumArrowLequivProdArrow (Fin 2) (Fin 2 ⊕ Fin 2) F4 F4).trans <|
      LinearEquiv.prodCongr (LinearEquiv.refl F4 TorusBlockV2)
        (LinearEquiv.sumArrowLequivProdArrow (Fin 2) (Fin 2) F4 F4)

def torusTripleMap
    (f₁ f₂ f₃ : Module.End F4 TorusBlockV2) : Module.End F4 TorusBlockTriple :=
  f₁.prodMap (f₂.prodMap f₃)

theorem torusBlockEquiv_conj_sl6End_coordBlock01 (A : SL2F4) :
    torusBlockEquiv.conj (sl6End F4 (coordBlock01 A)) =
      torusTripleMap (Matrix.mulVecLin (A : Matrix (Fin 2) (Fin 2) F4)) 1 1 := by
  classical
  apply LinearMap.ext
  intro v
  rcases v with ⟨v₁, v₂, v₃⟩
  refine Prod.ext ?_ ?_
  · funext i
    fin_cases i <;>
      simp [torusBlockEquiv, torusBlockIdx, LinearEquiv.piCongrLeft, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, LinearEquiv.sumArrowLequivProdArrow_symm_apply_inl, LinearEquiv.sumArrowLequivProdArrow_symm_apply_inr, torusTripleMap, sl6End, coordBlock01,
        CFSG.RankThree.CALinearPrimary.slGL, CFSG.RankThree.CALinearPrimary.coe_slGL,
        Matrix.toLin'_apply, Matrix.mulVec_apply, dotProduct, pairEmbed_apply, Fin.sum_univ_six]
  · refine Prod.ext ?_ ?_
    · funext i
      fin_cases i <;>
        simp [torusBlockEquiv, torusBlockIdx, LinearEquiv.piCongrLeft, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, LinearEquiv.sumArrowLequivProdArrow_symm_apply_inl, LinearEquiv.sumArrowLequivProdArrow_symm_apply_inr, torusTripleMap, sl6End, coordBlock01,
          CFSG.RankThree.CALinearPrimary.slGL, CFSG.RankThree.CALinearPrimary.coe_slGL,
          Matrix.toLin'_apply, Matrix.mulVec_apply, dotProduct, pairEmbed_apply, Fin.sum_univ_six]
    · funext i
      fin_cases i <;>
        simp [torusBlockEquiv, torusBlockIdx, LinearEquiv.piCongrLeft, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, LinearEquiv.sumArrowLequivProdArrow_symm_apply_inl, LinearEquiv.sumArrowLequivProdArrow_symm_apply_inr, torusTripleMap, sl6End, coordBlock01,
          CFSG.RankThree.CALinearPrimary.slGL, CFSG.RankThree.CALinearPrimary.coe_slGL,
          Matrix.toLin'_apply, Matrix.mulVec_apply, dotProduct, pairEmbed_apply, Fin.sum_univ_six]


theorem torusBlockEquiv_conj_sl6End_coordBlock23 (A : SL2F4) :
    torusBlockEquiv.conj (sl6End F4 (coordBlock23 A)) =
      torusTripleMap 1 (Matrix.mulVecLin (A : Matrix (Fin 2) (Fin 2) F4)) 1 := by
  classical
  apply LinearMap.ext
  intro v
  rcases v with ⟨v₁, v₂, v₃⟩
  refine Prod.ext ?_ ?_
  · funext i
    fin_cases i <;>
      simp [torusBlockEquiv, torusBlockIdx, LinearEquiv.piCongrLeft, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, LinearEquiv.sumArrowLequivProdArrow_symm_apply_inl, LinearEquiv.sumArrowLequivProdArrow_symm_apply_inr, torusTripleMap, sl6End, coordBlock23,
        CFSG.RankThree.CALinearPrimary.slGL, CFSG.RankThree.CALinearPrimary.coe_slGL,
        Matrix.toLin'_apply, Matrix.mulVec_apply, dotProduct, pairEmbed_apply, Fin.sum_univ_six]
  · refine Prod.ext ?_ ?_
    · funext i
      fin_cases i <;>
        simp [torusBlockEquiv, torusBlockIdx, LinearEquiv.piCongrLeft, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, LinearEquiv.sumArrowLequivProdArrow_symm_apply_inl, LinearEquiv.sumArrowLequivProdArrow_symm_apply_inr, torusTripleMap, sl6End, coordBlock23,
          CFSG.RankThree.CALinearPrimary.slGL, CFSG.RankThree.CALinearPrimary.coe_slGL,
          Matrix.toLin'_apply, Matrix.mulVec_apply, dotProduct, pairEmbed_apply, Fin.sum_univ_six]
    · funext i
      fin_cases i <;>
        simp [torusBlockEquiv, torusBlockIdx, LinearEquiv.piCongrLeft, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, LinearEquiv.sumArrowLequivProdArrow_symm_apply_inl, LinearEquiv.sumArrowLequivProdArrow_symm_apply_inr, torusTripleMap, sl6End, coordBlock23,
          CFSG.RankThree.CALinearPrimary.slGL, CFSG.RankThree.CALinearPrimary.coe_slGL,
          Matrix.toLin'_apply, Matrix.mulVec_apply, dotProduct, pairEmbed_apply, Fin.sum_univ_six]


theorem torusBlockEquiv_conj_sl6End_coordBlock45 (A : SL2F4) :
    torusBlockEquiv.conj (sl6End F4 (coordBlock45 A)) =
      torusTripleMap 1 1 (Matrix.mulVecLin (A : Matrix (Fin 2) (Fin 2) F4)) := by
  classical
  apply LinearMap.ext
  intro v
  rcases v with ⟨v₁, v₂, v₃⟩
  refine Prod.ext ?_ ?_
  · funext i
    fin_cases i <;>
      simp [torusBlockEquiv, torusBlockIdx, LinearEquiv.piCongrLeft, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, LinearEquiv.sumArrowLequivProdArrow_symm_apply_inl, LinearEquiv.sumArrowLequivProdArrow_symm_apply_inr, torusTripleMap, sl6End, coordBlock45,
        CFSG.RankThree.CALinearPrimary.slGL, CFSG.RankThree.CALinearPrimary.coe_slGL,
        Matrix.toLin'_apply, Matrix.mulVec_apply, dotProduct, pairEmbed_apply, Fin.sum_univ_six]
  · refine Prod.ext ?_ ?_
    · funext i
      fin_cases i <;>
        simp [torusBlockEquiv, torusBlockIdx, LinearEquiv.piCongrLeft, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, LinearEquiv.sumArrowLequivProdArrow_symm_apply_inl, LinearEquiv.sumArrowLequivProdArrow_symm_apply_inr, torusTripleMap, sl6End, coordBlock45,
          CFSG.RankThree.CALinearPrimary.slGL, CFSG.RankThree.CALinearPrimary.coe_slGL,
          Matrix.toLin'_apply, Matrix.mulVec_apply, dotProduct, pairEmbed_apply, Fin.sum_univ_six]
    · funext i
      fin_cases i <;>
        simp [torusBlockEquiv, torusBlockIdx, LinearEquiv.piCongrLeft, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, LinearEquiv.sumArrowLequivProdArrow_symm_apply_inl, LinearEquiv.sumArrowLequivProdArrow_symm_apply_inr, torusTripleMap, sl6End, coordBlock45,
          CFSG.RankThree.CALinearPrimary.slGL, CFSG.RankThree.CALinearPrimary.coe_slGL,
          Matrix.toLin'_apply, Matrix.mulVec_apply, dotProduct, pairEmbed_apply, Fin.sum_univ_six]


theorem sl6End_mul (a b : SL6F4) :
    sl6End F4 (a * b) = sl6End F4 a * sl6End F4 b := by
  simp [sl6End, map_mul]

theorem torusBlockEquiv_conj_mul
    (f g : Module.End F4 (Fin 6 → F4)) :
    torusBlockEquiv.conj (f * g) =
      torusBlockEquiv.conj f * torusBlockEquiv.conj g := by
  apply LinearMap.ext
  intro v
  simp [LinearEquiv.conj_apply, Module.End.mul_apply]

theorem torusBlockEquiv_conj_sl6End_product
    (A₁ A₂ A₃ : SL2F4) :
    torusBlockEquiv.conj
        (sl6End F4 (coordBlock01 A₁ * (coordBlock23 A₂ * coordBlock45 A₃))) =
      torusTripleMap
        (Matrix.mulVecLin (A₁ : Matrix (Fin 2) (Fin 2) F4))
        (Matrix.mulVecLin (A₂ : Matrix (Fin 2) (Fin 2) F4))
        (Matrix.mulVecLin (A₃ : Matrix (Fin 2) (Fin 2) F4)) := by
  rw [sl6End_mul, sl6End_mul, torusBlockEquiv_conj_mul, torusBlockEquiv_conj_mul,
    torusBlockEquiv_conj_sl6End_coordBlock01,
    torusBlockEquiv_conj_sl6End_coordBlock23,
    torusBlockEquiv_conj_sl6End_coordBlock45]
  simp [torusTripleMap, LinearMap.prodMap_mul]


theorem coordA2_zpow_pow_five (k : ℤ) : (coordA2 ^ k) ^ 5 = 1 := by
  rw [← zpow_natCast, ← zpow_mul, zpow_eq_one_iff_modEq, coordA2_order]
  rw [Int.modEq_zero_iff_dvd]
  simpa [mul_comm] using dvd_mul_left (5 : ℤ) k

theorem exists_coordinateTorus_decomposition {a : SL6F4}
    (ha : a ∈ coordinateTorus) :
    ∃ A₁ A₂ A₃ : SL2F4,
      A₁ ^ 5 = 1 ∧ A₂ ^ 5 = 1 ∧ A₃ ^ 5 = 1 ∧
      a = coordBlock01 A₁ * (coordBlock23 A₂ * coordBlock45 A₃) ∧
      coordBlock01 A₁ ∈ coordT01 ∧
      coordBlock23 A₂ ∈ coordT23 ∧
      coordBlock45 A₃ ∈ coordT45 := by
  classical
  change a ∈ coordT01 ⊔ (coordT23 ⊔ coordT45) at ha
  rw [CFSG.SignalizerFunctorTheorem.McBride.mem_sup_iff_of_commute
    (fun x hx y hy => coordT01_commutes_coordT23_45 hx hy)] at ha
  rcases ha with ⟨x, hx, y, hy, hxy⟩
  rw [CFSG.SignalizerFunctorTheorem.McBride.mem_sup_iff_of_commute
    (fun x hx y hy => coordT23_45_commute hx hy)] at hy
  rcases hy with ⟨z, hz, w, hw, hzw⟩
  rcases Subgroup.mem_zpowers_iff.mp hx with ⟨k₁, hk₁⟩
  rcases Subgroup.mem_zpowers_iff.mp hz with ⟨k₂, hk₂⟩
  rcases Subgroup.mem_zpowers_iff.mp hw with ⟨k₃, hk₃⟩
  let A₁ : SL2F4 := coordA2 ^ k₁
  let A₂ : SL2F4 := coordA2 ^ k₂
  let A₃ : SL2F4 := coordA2 ^ k₃
  have hA₁ : coordBlock01 A₁ = x := by
    rw [show A₁ = coordA2 ^ k₁ from rfl, map_zpow, hk₁]
  have hA₂ : coordBlock23 A₂ = z := by
    rw [show A₂ = coordA2 ^ k₂ from rfl, map_zpow, hk₂]
  have hA₃ : coordBlock45 A₃ = w := by
    rw [show A₃ = coordA2 ^ k₃ from rfl, map_zpow, hk₃]
  refine ⟨A₁, A₂, A₃, coordA2_zpow_pow_five k₁, coordA2_zpow_pow_five k₂,
    coordA2_zpow_pow_five k₃, ?_, ?_, ?_, ?_⟩
  · calc
      a = x * y := hxy.symm
      _ = x * (z * w) := by rw [← hzw]
      _ = coordBlock01 A₁ * (coordBlock23 A₂ * coordBlock45 A₃) := by
        rw [← hA₁, ← hA₂, ← hA₃]
  · rw [hA₁]
    exact hx
  · rw [hA₂]
    exact hz
  · rw [hA₃]
    exact hw


theorem fixedSubmodule_prodMap
    {R M N : Type*} [Semiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N]
    (f : Module.End R M) (g : Module.End R N) :
    (f.prodMap g).fixedSubmodule = f.fixedSubmodule.prod g.fixedSubmodule := by
  ext x
  simp [LinearMap.mem_fixedSubmodule_iff, Submodule.mem_prod, LinearMap.prodMap_apply, Prod.ext_iff]

theorem finrank_fixed_prodMap
    {R M N : Type*} [Field R] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] [FiniteDimensional R M] [FiniteDimensional R N]
    (f : Module.End R M) (g : Module.End R N) :
    Module.finrank R (f.prodMap g).fixedSubmodule =
      Module.finrank R f.fixedSubmodule + Module.finrank R g.fixedSubmodule := by
  letI : Module.Free R ↥f.fixedSubmodule := Module.Free.of_divisionRing R _
  letI : Module.Free R ↥g.fixedSubmodule := Module.Free.of_divisionRing R _
  letI : Module.Finite R ↥f.fixedSubmodule :=
    FiniteDimensional.finiteDimensional_submodule f.fixedSubmodule
  letI : Module.Finite R ↥g.fixedSubmodule :=
    FiniteDimensional.finiteDimensional_submodule g.fixedSubmodule
  rw [fixedSubmodule_prodMap]
  exact (Submodule.prodEquiv f.fixedSubmodule g.fixedSubmodule).finrank_eq.trans
    (Module.finrank_prod)

theorem finrank_fixed_conj
    {R M N : Type*} [Field R] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N]
    (e : M ≃ₗ[R] N) (f : Module.End R M) :
    Module.finrank R f.fixedSubmodule =
      Module.finrank R (e.conj f).fixedSubmodule := by
  have hmap : Submodule.map (e : M →ₗ[R] N) f.fixedSubmodule =
      (e.conj f).fixedSubmodule := by
    ext w
    constructor
    · rintro ⟨v, hv, rfl⟩
      change f v = v at hv
      change (e.conj f) (e v) = e v
      simp [LinearEquiv.conj_apply, hv]
    · intro hw
      refine ⟨e.symm w, ?_, ?_⟩
      · change f (e.symm w) = e.symm w
        have h := congrArg e.symm hw
        simpa [LinearEquiv.conj_apply] using h
      · simp
  rw [← hmap]
  exact (e.submoduleMap f.fixedSubmodule).finrank_eq

theorem finrank_fixed_tripleMap
    (f₁ f₂ f₃ : Module.End F4 TorusBlockV2) :
    Module.finrank F4 (torusTripleMap f₁ f₂ f₃).fixedSubmodule =
      Module.finrank F4 f₁.fixedSubmodule +
        (Module.finrank F4 f₂.fixedSubmodule + Module.finrank F4 f₃.fixedSubmodule) := by
  rw [torusTripleMap, finrank_fixed_prodMap, finrank_fixed_prodMap]

theorem finrank_fixed_mulVecLin_eq_two_of_eq_one
    (B : SL2F4) (hB : B = 1) :
    Module.finrank F4
      (Matrix.mulVecLin (B : Matrix (Fin 2) (Fin 2) F4)).fixedSubmodule = 2 := by
  subst B
  have htop :
      (Matrix.mulVecLin ((1 : SL2F4) : Matrix (Fin 2) (Fin 2) F4)).fixedSubmodule = ⊤ := by
    ext v
    simp [LinearMap.mem_fixedSubmodule_iff]
  rw [htop, finrank_top, Module.finrank_fin_fun]

theorem finrank_fixed_mulVecLin_eq_zero_of_ne_one
    (B : SL2F4) (hB5 : B ^ 5 = 1) (hB1 : B ≠ 1) :
    Module.finrank F4
      (Matrix.mulVecLin (B : Matrix (Fin 2) (Fin 2) F4)).fixedSubmodule = 0 := by
  have hbot :
      (Matrix.mulVecLin (B : Matrix (Fin 2) (Fin 2) F4)).fixedSubmodule = ⊥ := by
    ext v
    rw [Submodule.mem_bot, LinearMap.mem_fixedSubmodule_iff, Matrix.mulVecLin_apply]
    constructor
    · intro hv
      exact sl2F4_no_fixed_of_orderFive B v hB5 hB1 hv
    · intro hv
      subst hv
      simp
  rw [hbot, finrank_bot]

noncomputable def sl2BlockFixedDim (B : SL2F4) : ℕ := by
  classical
  exact if B = 1 then 2 else 0

theorem finrank_fixed_mulVecLin
    (B : SL2F4) (hB5 : B ^ 5 = 1) :
    Module.finrank F4
      (Matrix.mulVecLin (B : Matrix (Fin 2) (Fin 2) F4)).fixedSubmodule =
        sl2BlockFixedDim B := by
  classical
  unfold sl2BlockFixedDim
  by_cases hB1 : B = 1
  · rw [if_pos hB1]
    exact finrank_fixed_mulVecLin_eq_two_of_eq_one B hB1
  · rw [if_neg hB1]
    exact finrank_fixed_mulVecLin_eq_zero_of_ne_one B hB5 hB1


theorem coordinateTorus_support_one {a : SL6F4}
    (haT : a ∈ coordinateTorus) (ha5 : orderOf a = 5)
    (hfix : sl6FixedMultiplicity F4 a = 4) :
    a ∈ coordT01 ∨ a ∈ coordT23 ∨ a ∈ coordT45 := by
  classical
  have hdim4 : Module.finrank F4 (sl6End F4 a).fixedSubmodule = 4 := by
    rw [← sl6FixedMultiplicity_eq_finrank_fixedSubmodule ha5, hfix]
  obtain ⟨A₁, A₂, A₃, hA₁, hA₂, hA₃, hdecomp, h01, h23, h45⟩ :=
    exists_coordinateTorus_decomposition haT
  have hconj : Module.finrank F4
      (torusBlockEquiv.conj
        (sl6End F4
          (coordBlock01 A₁ * (coordBlock23 A₂ * coordBlock45 A₃)))).fixedSubmodule = 4 := by
    rw [← finrank_fixed_conj torusBlockEquiv
      (sl6End F4 (coordBlock01 A₁ * (coordBlock23 A₂ * coordBlock45 A₃)))]
    rw [← hdecomp]
    exact hdim4
  rw [torusBlockEquiv_conj_sl6End_product, finrank_fixed_tripleMap,
    finrank_fixed_mulVecLin A₁ hA₁, finrank_fixed_mulVecLin A₂ hA₂,
    finrank_fixed_mulVecLin A₃ hA₃] at hconj
  by_cases h1 : A₁ = 1
  · by_cases h2 : A₂ = 1
    · by_cases h3 : A₃ = 1
      · exfalso
        simp [sl2BlockFixedDim, h1, h2, h3] at hconj
      · right; right
        rw [hdecomp]
        simpa [h1, h2, h3] using h45
    · by_cases h3 : A₃ = 1
      · right; left
        rw [hdecomp]
        simpa [h1, h2, h3] using h23
      · exfalso
        simp [sl2BlockFixedDim, h1, h2, h3] at hconj
  · by_cases h2 : A₂ = 1
    · by_cases h3 : A₃ = 1
      · left
        rw [hdecomp]
        simpa [h1, h2, h3] using h01
      · exfalso
        simp [sl2BlockFixedDim, h1, h2, h3] at hconj
    · by_cases h3 : A₃ = 1
      · exfalso
        simp [sl2BlockFixedDim, h1, h2, h3] at hconj
      · exfalso
        simp [sl2BlockFixedDim, h1, h2, h3] at hconj


end
end CFSG.StandardType.N2KCoordinate


public section

namespace CFSG.StandardType


end CFSG.StandardType


public section

namespace CFSG.StandardType.N2KAllNeighborComponent

open Matrix
open CFSG.Assembly
open CFSG.StandardType

noncomputable section


variable {G : Type} [Group G] [Finite G]

private theorem five_dvd_card_original_J
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G}
    {Rd Ra : Prop} (hR : GGSecFiveRestGen 5 B Bs x L D J Rd Ra)
    (hNbr : GGNbr 5 B x D J y K)
    (hL : GGCentralImage .POmegaMinus 4 2 L)
    (hK : GGCentralImage .PSL 6 2 K) :
    5 ∣ Nat.card J := by
  obtain ⟨-, ⟨F0, hField0, hFinite0, hChar0, hF0, ⟨eJ⟩⟩, -⟩ :=
    ggF4N2J_original_mixed_recognition hR hNbr hL hK
  letI : Field F0 := hField0
  letI : Finite F0 := hFinite0
  have hcardJ : Nat.card J = Nat.card (Matrix.SpecialLinearGroup (Fin 4) F0) :=
    Nat.card_congr eJ.toEquiv
  rw [hcardJ, CFSG.OrderReductions.LinearOrders.card_specialLinear F0 4 (by norm_num), hF0]
  have hmem : (2 : ℕ) ∈ Finset.Icc 2 4 := by norm_num
  have hfactor : 5 ∣ 4 ^ 2 - 1 := by norm_num
  have hprod : 5 ∣ ∏ index ∈ Finset.Icc 2 4, (4 ^ index - 1) :=
    hfactor.trans (Finset.dvd_prod_of_mem (fun index : ℕ => 4 ^ index - 1) hmem)
  exact dvd_mul_of_dvd_right hprod 4096

open Matrix
open scoped Pointwise


theorem arbitrary_neighbor_component
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G}
    {Rd Ra : Prop} (hR : GGSecFiveRestGen 5 B Bs x L D J Rd Ra)
    (hNbr : GGNbr 5 B x D J y K)
    (hL : GGCentralImage .POmegaMinus 4 2 L)
    (hK : GGCentralImage .PSL 6 2 K)
    (hLb : GGLBalanceInput) :
    ∀ (d : G) (Y : Subgroup G), GGNbr 5 B x D J d Y →
      J ≤ Y ∧ IsComponentOf J (Y ⊓ Subgroup.centralizer ({x} : Set G)) := by
  intro d Y hNY
  have hI : GGThmIHyp 5 B x L := hR.1.1
  have hDJ : LargeEvenStdSub 5 B x L D J := hR.1.2.2
  have hS : LargeEvenSStar 5 B x L := hR.1.1.2.2.2.2.2.2.1
  have h5J : 5 ∣ Nat.card J := five_dvd_card_original_J hR hNbr hL hK
  have hJY : J ≤ Y := le_of_ggNbr hLb hI hDJ h5J hNY
  exact ⟨hJY, isComponentOf_inf_centralizer_of_ggNbr hS hDJ hNY hJY⟩

end

end CFSG.StandardType.N2KAllNeighborComponent

namespace CFSG.StandardType.N2KCoordinate

open CFSG.SeitzReduction.LinearPilot
open CFSG.SeitzReduction.E6Pilot
open CFSG.RankThree.CALinearPrimary
open CFSG.RankThree.PartOne.KCPrimary
open Matrix Polynomial

noncomputable section

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

private def split46 : (Fin 6 → F4) ≃ₗ[F4] ((Fin 4 → F4) × (Fin 2 → F4)) where
  toFun v := (fun i => v (e46 (Sum.inl i)), fun j => v (e46 (Sum.inr j)))
  invFun p := fun k => Sum.elim p.1 p.2 (e46.symm k)
  map_add' v w := by ext <;> simp
  map_smul' c v := by ext <;> simp
  left_inv v := by
    ext k
    cases h : e46.symm k with
    | inl i =>
        have hk : e46 (Sum.inl i) = k := by rw [← h, e46.apply_symm_apply]
        change Sum.elim (fun i => v (e46 (Sum.inl i)))
          (fun j => v (e46 (Sum.inr j))) (e46.symm k) = v k
        rw [h]
        simp [hk]
    | inr j =>
        have hk : e46 (Sum.inr j) = k := by rw [← h, e46.apply_symm_apply]
        change Sum.elim (fun i => v (e46 (Sum.inl i)))
          (fun j => v (e46 (Sum.inr j))) (e46.symm k) = v k
        rw [h]
        simp [hk]
  right_inv p := by
    ext i <;> simp

@[simp]
private theorem split46_apply (v : Fin 6 → F4) :
    split46 v = (fun i => v (e46 (Sum.inl i)), fun j => v (e46 (Sum.inr j))) := rfl

@[simp]
private theorem split46_symm_apply (x : Fin 4 → F4) (y : Fin 2 → F4) (k : Fin 6) :
    split46.symm (x, y) k = Sum.elim x y (e46.symm k) := rfl

private def block45End (A : SL2F4) : Module.End F4 (Fin 6 → F4) := sl6End F4 (coordBlock45 A)

private theorem split46_block45End_apply (A : SL2F4) (x : Fin 4 → F4) (y : Fin 2 → F4) :
    split46 (block45End A (split46.symm (x, y))) =
      (x, (A : Matrix (Fin 2) (Fin 2) F4).mulVec y) := by
  classical
  apply Prod.ext
  · funext i
    fin_cases i <;>
      simp [split46, block45End, sl6End, coordBlock45,
        CFSG.RankThree.CALinearPrimary.slGL, pairEmbed_apply,
        Matrix.toLin'_apply, Matrix.mulVec_apply, dotProduct, Fin.sum_univ_six, e46, Matrix.one_apply]
  · funext j
    fin_cases j <;>
      simp [split46, block45End, sl6End, coordBlock45,
        CFSG.RankThree.CALinearPrimary.slGL, pairEmbed_apply,
        Matrix.toLin'_apply, Matrix.mulVec_apply, dotProduct, Fin.sum_univ_six, e46, Matrix.one_apply]


private theorem blockFourMat_mulVec_fst (A : Matrix.SpecialLinearGroup (Fin 4) F4)
    (v : Fin 6 → F4) (i : Fin 4) :
    ((blockFourMat (A : Matrix (Fin 4) (Fin 4) F4)).mulVec v) (e46 (Sum.inl i)) =
      ((A : Matrix (Fin 4) (Fin 4) F4).mulVec (split46 v).1) i := by
  classical
  rw [Matrix.mulVec, dotProduct, Matrix.mulVec, dotProduct]
  rw [show (∑ k : Fin 6,
        blockFourMat (A : Matrix (Fin 4) (Fin 4) F4) (e46 (Sum.inl i)) k * v k) =
      ∑ s : Fin 4 ⊕ Fin 2,
        blockFourMat (A : Matrix (Fin 4) (Fin 4) F4) (e46 (Sum.inl i)) (e46 s) *
          v (e46 s) from
    (Fintype.sum_equiv e46
      (fun s : Fin 4 ⊕ Fin 2 =>
        blockFourMat (A : Matrix (Fin 4) (Fin 4) F4) (e46 (Sum.inl i)) (e46 s) * v (e46 s))
      (fun k : Fin 6 => blockFourMat (A : Matrix (Fin 4) (Fin 4) F4) (e46 (Sum.inl i)) k * v k)
      (by intro s; rfl)).symm]
  have hv : ∀ s : Fin 4 ⊕ Fin 2,
      v (e46 s) = Sum.elim (split46 v).1 (split46 v).2 s := by
    intro s
    cases s <;> rfl
  rw [Fintype.sum_sum_type]
  simp only [hv, blockFourMat_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.one_apply,
    Matrix.zero_apply, Sum.elim_inl, Sum.elim_inr, Matrix.mulVec, dotProduct,
    Fin.sum_univ_four, Fin.sum_univ_two, mul_zero, zero_mul, add_zero, zero_add]

private theorem blockFourMat_mulVec_snd (A : Matrix.SpecialLinearGroup (Fin 4) F4)
    (v : Fin 6 → F4) (i : Fin 2) :
    ((blockFourMat (A : Matrix (Fin 4) (Fin 4) F4)).mulVec v) (e46 (Sum.inr i)) =
      (split46 v).2 i := by
  classical
  rw [Matrix.mulVec, dotProduct]
  rw [show (∑ k : Fin 6,
        blockFourMat (A : Matrix (Fin 4) (Fin 4) F4) (e46 (Sum.inr i)) k * v k) =
      ∑ s : Fin 4 ⊕ Fin 2,
        blockFourMat (A : Matrix (Fin 4) (Fin 4) F4) (e46 (Sum.inr i)) (e46 s) *
          v (e46 s) from
    (Fintype.sum_equiv e46
      (fun s : Fin 4 ⊕ Fin 2 =>
        blockFourMat (A : Matrix (Fin 4) (Fin 4) F4) (e46 (Sum.inr i)) (e46 s) * v (e46 s))
      (fun k : Fin 6 => blockFourMat (A : Matrix (Fin 4) (Fin 4) F4) (e46 (Sum.inr i)) k * v k)
      (by intro s; rfl)).symm]
  have hv : ∀ s : Fin 4 ⊕ Fin 2,
      v (e46 s) = Sum.elim (split46 v).1 (split46 v).2 s := by
    intro s
    cases s <;> rfl
  rw [Fintype.sum_sum_type]
  simp only [hv, blockFourMat_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.one_apply,
    Matrix.zero_apply, Sum.elim_inl, Sum.elim_inr, Matrix.mulVec, dotProduct,
    Fin.sum_univ_four, Fin.sum_univ_two, mul_zero, zero_mul, add_zero, zero_add]
  fin_cases i <;> simp

private theorem split46_mulVec_blockFourMat (A : Matrix.SpecialLinearGroup (Fin 4) F4)
    (v : Fin 6 → F4) :
    split46 ((blockFourMat (A : Matrix (Fin 4) (Fin 4) F4)).mulVec v) =
      ((A : Matrix (Fin 4) (Fin 4) F4).mulVec (split46 v).1, (split46 v).2) := by
  apply Prod.ext
  · funext i
    exact blockFourMat_mulVec_fst A v i
  · funext j
    exact blockFourMat_mulVec_snd A v j


private def firstCoord : Submodule F4 (Fin 6 → F4) :=
  Submodule.comap split46.toLinearMap
    (Submodule.prod (⊤ : Submodule F4 (Fin 4 → F4)) (⊥ : Submodule F4 (Fin 2 → F4)))

private def lastCoord : Submodule F4 (Fin 6 → F4) :=
  Submodule.comap split46.toLinearMap
    (Submodule.prod (⊥ : Submodule F4 (Fin 4 → F4)) (⊤ : Submodule F4 (Fin 2 → F4)))

private theorem mem_firstCoord {v : Fin 6 → F4} :
    v ∈ firstCoord ↔ (split46 v).2 = 0 := by
  simp [firstCoord, Submodule.mem_prod]

private theorem mem_lastCoord {v : Fin 6 → F4} :
    v ∈ lastCoord ↔ (split46 v).1 = 0 := by
  simp [lastCoord, Submodule.mem_prod]

private theorem fixedSubmodule_block45End (A : SL2F4)
    (hA : ∀ y : Fin 2 → F4, (A : Matrix (Fin 2) (Fin 2) F4).mulVec y = y → y = 0) :
    (block45End A).fixedSubmodule = firstCoord := by
  ext v
  generalize hxy : split46 v = p at *
  obtain ⟨x, y⟩ := p
  have hv : split46.symm (x, y) = v := by
    rw [← hxy]
    exact split46.symm_apply_apply v
  rw [LinearMap.mem_fixedSubmodule_iff, mem_firstCoord, hxy]
  constructor
  · intro hvmem
    have h := congrArg split46 hvmem
    rw [← hv] at h
    have h2 : (A : Matrix (Fin 2) (Fin 2) F4).mulVec y = y := by
      have h1 : (split46 (block45End A (split46.symm (x, y)))).2 = y := by
        rw [h]
        simp
      have h2' : (split46 (block45End A (split46.symm (x, y)))).2 =
          (A : Matrix (Fin 2) (Fin 2) F4).mulVec y := by
        rw [split46_block45End_apply]
      exact h2'.symm.trans h1
    exact hA y h2
  · intro hy
    change y = 0 at hy
    apply split46.injective
    rw [← hv, split46_block45End_apply, hy]
    simp

private theorem range_block45End_sub_one (A : SL2F4)
    (hA : ∀ y : Fin 2 → F4, (A : Matrix (Fin 2) (Fin 2) F4).mulVec y = y → y = 0) :
    LinearMap.range ((block45End A) - (1 : Module.End F4 (Fin 6 → F4))) = lastCoord := by
  classical
  let Alin : Module.End F4 (Fin 2 → F4) := Matrix.mulVecLin (A : Matrix (Fin 2) (Fin 2) F4)
  have hker : LinearMap.ker (Alin - (1 : Module.End F4 (Fin 2 → F4))) = ⊥ := by
    ext y
    rw [LinearMap.mem_ker, Submodule.mem_bot]
    constructor
    · intro hy
      apply hA y
      funext i
      have hi := congrFun hy i
      simpa [Alin, LinearMap.sub_apply, sub_eq_zero] using hi
    · intro hy
      simp [hy]
  have hsurj : Function.Surjective (Alin - (1 : Module.End F4 (Fin 2 → F4))) := by
    rw [← LinearMap.range_eq_top, ← LinearMap.ker_eq_bot_iff_range_eq_top]
    exact hker
  have hsplit : ∀ (x' : Fin 4 → F4) (y' : Fin 2 → F4),
      split46 (((block45End A) - (1 : Module.End F4 (Fin 6 → F4)))
        (split46.symm (x', y'))) = (0, (Alin - (1 : Module.End F4 (Fin 2 → F4))) y') := by
    intro x' y'
    rw [LinearMap.sub_apply, map_sub, split46_block45End_apply]
    simp [Alin, LinearMap.sub_apply]
  ext v
  generalize hxy : split46 v = p at *
  obtain ⟨x, y⟩ := p
  rw [LinearMap.mem_range, mem_lastCoord, hxy]
  constructor
  · rintro ⟨w, hw⟩
    generalize hwxy : split46 w = q at *
    obtain ⟨x', y'⟩ := q
    have hwv : w = split46.symm (x', y') := by
      rw [← hwxy]
      exact (split46.symm_apply_apply w).symm
    have h := congrArg split46 hw
    rw [hwv, hsplit, hxy] at h
    exact (Prod.ext_iff.mp h).1.symm
  · intro hx
    change x = 0 at hx
    obtain ⟨y', hy'⟩ := hsurj y
    refine ⟨split46.symm (0, y'), ?_⟩
    apply split46.injective
    rw [hsplit, hy', hxy, hx]

private theorem orderOf_coordBlock45 (A : SL2F4) :
    orderOf (coordBlock45 A) = orderOf A :=
  orderOf_injective coordBlock45 coordBlock45_injective A

private theorem split46_submoduleMap_firstCoord :
    Submodule.map (split46 : (Fin 6 → F4) →ₗ[F4] ((Fin 4 → F4) × (Fin 2 → F4)))
        firstCoord =
      Submodule.prod (⊤ : Submodule F4 (Fin 4 → F4)) (⊥ : Submodule F4 (Fin 2 → F4)) := by
  ext p
  constructor
  · rintro ⟨v, hv, rfl⟩
    have hv2 : (split46 v).2 = 0 := mem_firstCoord.mp hv
    simpa [split46] using hv2
  · intro hp
    have hp2 : p.2 = 0 := by simpa using hp
    refine ⟨split46.symm (p.1, 0), ?_, ?_⟩
    · exact mem_firstCoord.mpr (by simp)
    · ext <;> simp [hp2]

private theorem finrank_firstCoord : Module.finrank F4 firstCoord = 4 := by
  rw [← LinearEquiv.finrank_map_eq split46 firstCoord, split46_submoduleMap_firstCoord]
  calc Module.finrank F4 ↥(Submodule.prod (⊤ : Submodule F4 (Fin 4 → F4))
        (⊥ : Submodule F4 (Fin 2 → F4)))
      = Module.finrank F4 ((⊤ : Submodule F4 (Fin 4 → F4)) ×
          (⊥ : Submodule F4 (Fin 2 → F4))) :=
        (Submodule.prodEquiv _ _).finrank_eq
    _ = 4 := by rw [Module.finrank_prod]; simp

private theorem coordBlock45_no_fixed (A : SL2F4) (hAord : orderOf A = 5) (hA1 : A ≠ 1) :
    ∀ y : Fin 2 → F4, (A : Matrix (Fin 2) (Fin 2) F4).mulVec y = y → y = 0 := by
  intro y hy
  refine CFSG.CGT.PushingUpLit.CGT6.eq_zero_of_fixed_vec_of_odd_order
    (x := A) ?_ hA1 hy
  rw [hAord]
  exact ⟨2, by norm_num⟩

private theorem sl6FixedMultiplicity_coordBlock45_eq_four (A : SL2F4) (hAord : orderOf A = 5)
    (hA1 : A ≠ 1) :
    sl6FixedMultiplicity F4 (coordBlock45 A) = 4 := by
  have hno := coordBlock45_no_fixed A hAord hA1
  rw [sl6FixedMultiplicity_eq_finrank_fixedSubmodule (a := coordBlock45 A) ?_]
  · change Module.finrank F4 (block45End A).fixedSubmodule = 4
    rw [fixedSubmodule_block45End A hno, finrank_firstCoord]
  · rwa [orderOf_coordBlock45 A]

private theorem exists_coordBlock45_of_mem_coordT45 {a : SL6F4} (ha : a ∈ coordT45) :
    ∃ A : SL2F4, a = coordBlock45 A := by
  rw [coordT45, Subgroup.mem_zpowers_iff] at ha
  obtain ⟨k, rfl⟩ := ha
  exact ⟨coordA2 ^ k, by rw [map_zpow]⟩


private theorem split46_blockFour_apply_arbitrary (A : Matrix.SpecialLinearGroup (Fin 4) F4)
    (v : Fin 6 → F4) :
    split46 ((Matrix.toLin' (blockFour A)) v) =
      ((A : Matrix (Fin 4) (Fin 4) F4).mulVec (split46 v).1, (split46 v).2) := by
  have h := split46_mulVec_blockFourMat A v
  simpa [Matrix.toLin'_apply, coe_blockFour] using h


private theorem X_sub_one_mem_primaryFactors (A0 : SL2F4) (hAord : orderOf A0 = 5)
    (hA1 : A0 ≠ 1) :
    (X - 1 : F4[X]) ∈ primaryFactors (sl6End F4 (coordBlock45 A0)) := by
  classical
  let v : Fin 6 → F4 := split46.symm (Pi.single (0 : Fin 4) (1 : F4), 0)
  have hvne : v ≠ 0 := by
    intro h
    have hsplit := congrArg split46 h
    have h0 : (split46 v).1 0 = 0 := congrArg (fun p : (Fin 4 → F4) × (Fin 2 → F4) => p.1 0) hsplit
    simp [v] at h0
  have hvmem : v ∈ primaryComponent (sl6End F4 (coordBlock45 A0)) (X - 1) := by
    rw [← sl6End_fixedSubmodule_eq_primaryComponent]
    change v ∈ (block45End A0).fixedSubmodule
    rw [fixedSubmodule_block45End A0 (coordBlock45_no_fixed A0 hAord hA1)]
    exact mem_firstCoord.mpr (by simp [v])
  exact CFSG.RankThree.PartOne.KCLinPlane.mem_primaryFactors_of_ne_zero
    CFSG.RankThree.Classical.irreducible_X_sub_one
    CFSG.RankThree.Classical.monic_X_sub_one hvne hvmem


private def firstCoordEquiv : firstCoord ≃ₗ[F4] (Fin 4 → F4) where
  toFun v := (split46 (v : Fin 6 → F4)).1
  invFun x := ⟨split46.symm (x, 0), mem_firstCoord.mpr (by simp)⟩
  map_add' v w := by
    ext i
    simp
  map_smul' c v := by
    ext i
    simp
  left_inv v := by
    apply Subtype.ext
    apply split46.injective
    change split46 (split46.symm ((split46 (v : Fin 6 → F4)).1, 0)) =
      split46 (v : Fin 6 → F4)
    rw [show split46 (split46.symm ((split46 (v : Fin 6 → F4)).1, 0)) =
        ((split46 (v : Fin 6 → F4)).1, 0) by simp]
    apply Prod.ext
    · rfl
    · funext j
      simpa using (congrFun (mem_firstCoord.mp v.2) j).symm
  right_inv x := by
    ext i
    change (split46 (split46.symm (x, 0))).1 i = x i
    simp

@[simp]
private theorem firstCoordEquiv_apply (v : firstCoord) :
    firstCoordEquiv v = (split46 (v : Fin 6 → F4)).1 := rfl

private theorem primaryComponent_eq_firstCoord (A0 : SL2F4) (hAord : orderOf A0 = 5)
    (hA1 : A0 ≠ 1) :
    primaryComponent (sl6End F4 (coordBlock45 A0)) (X - 1) = firstCoord := by
  rw [← sl6End_fixedSubmodule_eq_primaryComponent]
  exact fixedSubmodule_block45End A0 (coordBlock45_no_fixed A0 hAord hA1)

private noncomputable def adjRootXSubOneEquiv (F : Type) [Field F] [Finite F]
    (hF : Nat.card F = 4) : AdjoinRoot (X - 1 : F[X]) ≃+* F := by
  classical
  let φ : AdjoinRoot (X - 1 : F[X]) →+* F :=
    AdjoinRoot.lift (RingHom.id F) 1 (by
      simpa using eval₂_X_sub_C (RingHom.id F) 1)
  haveI : Fact (Irreducible (X - 1 : F[X])) := ⟨irreducible_X_sub_C 1⟩
  have hinj : Function.Injective φ := RingHom.injective φ
  have hdeg : (X - 1 : F[X]).natDegree = 1 := by
    simpa using natDegree_X_sub_C (1 : F)
  have hcard : Nat.card (AdjoinRoot (X - 1 : F[X])) = Nat.card F := by
    rw [CFSG.RankThree.PartOne.KCLinPlane.natCard_adjoinRoot, hdeg, hF]
    norm_num
  exact RingEquiv.ofBijective φ
    ((Nat.bijective_iff_injective_and_card φ).mpr ⟨hinj, hcard⟩)

private noncomputable def slMapEquiv4 {F E : Type} [Field F] [Field E]
    (e : F ≃+* E) :
    Matrix.SpecialLinearGroup (Fin 4) F ≃*
      Matrix.SpecialLinearGroup (Fin 4) E where
  toFun := Matrix.SpecialLinearGroup.map e.toRingHom
  invFun := Matrix.SpecialLinearGroup.map e.symm.toRingHom
  left_inv g := by
    ext i j
    change e.symm (e ((g : Matrix (Fin 4) (Fin 4) F) i j)) =
      (g : Matrix (Fin 4) (Fin 4) F) i j
    simp
  right_inv g := by
    ext i j
    change e (e.symm ((g : Matrix (Fin 4) (Fin 4) E) i j)) =
      (g : Matrix (Fin 4) (Fin 4) E) i j
    simp
  map_mul' g h := map_mul (Matrix.SpecialLinearGroup.map e.toRingHom) g h

private theorem natCard_linearSpecialBlock_comap (A0 : SL2F4) (hAord : orderOf A0 = 5)
    (hA1 : A0 ≠ 1) :
    Nat.card (((linearSpecialBlock (slGL 6 F4 (coordBlock45 A0)) (X - 1)).comap
      (slGL 6 F4))) = Nat.card (Matrix.SpecialLinearGroup (Fin 4) F4) := by
  classical
  let a : SL6F4 := coordBlock45 A0
  let B : Subgroup SL6F4 := (linearSpecialBlock (slGL 6 F4 a) (X - 1)).comap (slGL 6 F4)
  have hsq0 : Squarefree (minpoly F4 ((slGL 6 F4 a :
      LinearMap.GeneralLinearGroup F4 (Fin 6 → F4)) : Module.End F4 (Fin 6 → F4))) := by
    have h5 : (5 : F4) ≠ 0 :=
      CharP.cast_ne_zero_of_ne_of_prime (R := F4) (p := 2) (q := 5) (by norm_num) (by norm_num)
    refine squarefree_minpoly_slGL (n := 6) (k := F4) (p := 5) h5 ?_
    have hpow : (coordBlock45 A0) ^ 5 = 1 := by
      have hord : orderOf (coordBlock45 A0) = 5 := by
        rw [orderOf_coordBlock45, hAord]
      have := pow_orderOf_eq_one (coordBlock45 A0)
      rwa [hord] at this
    simpa [a] using hpow
  have hhGL : (X - 1 : F4[X]) ∈ primaryFactors
      ((slGL 6 F4 a : LinearMap.GeneralLinearGroup F4 (Fin 6 → F4)) :
        Module.End F4 (Fin 6 → F4)) := by
    simpa [sl6End, a] using X_sub_one_mem_primaryFactors A0 hAord hA1
  have hmem6 : (X - 1 : F4[X]) ∈ primaryFactors (sl6End F4 a) := by
    simpa [sl6End, a] using hhGL
  have hmult : primaryMultiplicity (sl6End F4 a) (X - 1) = 4 := by
    rw [← sl6FixedMultiplicity_eq_of_fixed hmem6 rfl,
      sl6FixedMultiplicity_coordBlock45_eq_four A0 hAord hA1]
  have hmBGL : primaryMultiplicity
      ((slGL 6 F4 a : LinearMap.GeneralLinearGroup F4 (Fin 6 → F4)) :
        Module.End F4 (Fin 6 → F4)) (X - 1) = 4 := by
    simpa [sl6End, a] using hmult
  obtain ⟨eB⟩ := CFSG.RankThree.CALinearPrimary.comap_linearSpecialBlock_mulEquiv
    (n := 6) (k := F4) (a := a) hsq0 hhGL
  let e1 : linearSpecialBlock (slGL 6 F4 a) (X - 1) ≃*
      _root_.SpecialLinearGroup (AdjoinRoot (X - 1 : F4[X]))
        (primaryComponent ((slGL 6 F4 a : LinearMap.GeneralLinearGroup F4 (Fin 6 → F4)) :
          Module.End F4 (Fin 6 → F4)) (X - 1)) :=
    MulEquiv.ofBijective
      (CFSG.RankThree.CALinearPrimary.linearSpecialBlockRestrict (slGL 6 F4 a) (X - 1))
      ⟨CFSG.RankThree.CALinearPrimary.linearSpecialBlockRestrict_injective
          (x := slGL 6 F4 a) hsq0,
        CFSG.RankThree.CALinearPrimary.linearSpecialBlockRestrict_surjective
          (x := slGL 6 F4 a) hsq0 hhGL⟩
  haveI : Fact (Irreducible (X - 1 : F4[X])) := ⟨irreducible_of_mem_primaryFactors hhGL⟩
  haveI : Finite (AdjoinRoot (X - 1 : F4[X])) := Module.finite_of_finite F4
  let basis : Module.Basis (Fin 4) (AdjoinRoot (X - 1 : F4[X]))
      (primaryComponent ((slGL 6 F4 a : LinearMap.GeneralLinearGroup F4 (Fin 6 → F4)) :
        Module.End F4 (Fin 6 → F4)) (X - 1)) :=
    Module.finBasisOfFinrankEq _ _ (by simpa [primaryMultiplicity] using hmBGL)
  calc
    Nat.card B = Nat.card (linearSpecialBlock (slGL 6 F4 a) (X - 1)) :=
      Nat.card_congr eB.toEquiv
    _ = Nat.card (_root_.SpecialLinearGroup (AdjoinRoot (X - 1 : F4[X]))
          (primaryComponent ((slGL 6 F4 a : LinearMap.GeneralLinearGroup F4 (Fin 6 → F4)) :
            Module.End F4 (Fin 6 → F4)) (X - 1))) :=
      Nat.card_congr e1.toEquiv
    _ = Nat.card (Matrix.SpecialLinearGroup (Fin 4)
          (AdjoinRoot (X - 1 : F4[X]))) :=
      Nat.card_congr (Matrix.SpecialLinearGroup.toLin_equiv basis).symm.toEquiv
    _ = Nat.card (Matrix.SpecialLinearGroup (Fin 4) F4) :=
      Nat.card_congr (slMapEquiv4 (adjRootXSubOneEquiv F4 (by rw [GaloisField.card 2 2 (by norm_num)]; norm_num))).toEquiv


private theorem commute_aeval_local {A B : Module.End F4 (Fin 6 → F4)} (h : Commute A B)
    (q : F4[X]) : Commute A (aeval B q) := by
  induction q using Polynomial.induction_on' with
  | add p r hp hr => rw [map_add]; exact hp.add_right hr
  | monomial n c =>
      rw [Polynomial.aeval_monomial]
      exact (Algebra.commute_algebraMap_right c A).mul_right (h.pow_right n)

private theorem squarefree_sl6End_coordBlock45 (A0 : SL2F4) (hAord : orderOf A0 = 5) :
    Squarefree (minpoly F4 (sl6End F4 (coordBlock45 A0))) := by
  have h5 : (5 : F4) ≠ 0 :=
    CharP.cast_ne_zero_of_ne_of_prime (R := F4) (p := 2) (q := 5) (by norm_num) (by norm_num)
  have hpow : (coordBlock45 A0) ^ 5 = 1 := by
    have hord : orderOf (coordBlock45 A0) = 5 := by
      rw [orderOf_coordBlock45, hAord]
    have := pow_orderOf_eq_one (coordBlock45 A0)
    rwa [hord] at this
  simpa [sl6End] using squarefree_minpoly_slGL (n := 6) (k := F4) (p := 5) h5 hpow

private theorem gEnd_fixes_lastCoord (g : SL6F4) (A0 : SL2F4) (hAord : orderOf A0 = 5)
    (hA1 : A0 ≠ 1)
    (hgB : g ∈ (linearSpecialBlock (slGL 6 F4 (coordBlock45 A0)) (X - 1)).comap (slGL 6 F4)) :
    ∀ v ∈ lastCoord, sl6End F4 g v = v := by
  classical
  let T := sl6End F4 (coordBlock45 A0)
  have hsq : Squarefree (minpoly F4 T) := squarefree_sl6End_coordBlock45 A0 hAord
  have hno := coordBlock45_no_fixed A0 hAord hA1
  have hg1 := Subgroup.mem_comap.mp hgB
  have hgcomm : Commute (sl6End F4 g) T := by
    have := CFSG.RankThree.PartOne.KCUnitary.mem_gl_centralizer.mp hg1.1
    simpa [sl6End, T] using this
  have hgfix : ∀ j ∈ primaryFactors T, j ≠ X - 1 →
      ∀ v ∈ primaryComponent T j, sl6End F4 g v = v := by
    intro j hj hj1 v hv
    have := hg1.2.1 j hj hj1 v hv
    simpa [sl6End, T] using this
  intro v hv
  have hvrange : v ∈ LinearMap.range (T - 1) := by
    change v ∈ LinearMap.range (block45End A0 - 1)
    rw [range_block45End_sub_one A0 hno]
    exact hv
  obtain ⟨w, hw⟩ := hvrange
  have hkill : (T - 1) (sl6End F4 g w - w) = 0 := by
    let z : Fin 6 → F4 := (T - 1) (sl6End F4 g w - w)
    have hz : primaryEquivPi hsq z = 0 := by
      funext j
      apply Subtype.ext
      funext x
      have hprojzero : primaryProjection T (j : F4[X]) z = 0 := by
        have hprojT : Commute (T - 1) (primaryProjection T (j : F4[X])) := by
          have h : Commute T (primaryProjection T (j : F4[X])) :=
            commute_aeval_local (Commute.refl T) (primaryIdempotent T (j : F4[X]))
          exact h.sub_left (Commute.one_left (primaryProjection T (j : F4[X])))
        have hprojg : Commute (sl6End F4 g) (primaryProjection T (j : F4[X])) :=
          commute_aeval_local hgcomm (primaryIdempotent T (j : F4[X]))
        change (primaryProjection T (j : F4[X]))
          ((T - 1) (sl6End F4 g w - w)) = 0
        change ((primaryProjection T (j : F4[X])) * (T - 1))
          (sl6End F4 g w - w) = 0
        rw [← hprojT.eq]
        change (T - 1) (primaryProjection T (j : F4[X]) (sl6End F4 g w - w)) = 0
        by_cases hj : (j : F4[X]) = X - 1
        · have hcomp : primaryProjection T (j : F4[X])
              (sl6End F4 g w - w) ∈ primaryComponent T (X - 1) := by
            rw [← hj]
            exact primaryProjection_mem hsq j.2 (sl6End F4 g w - w)
          have hzmem : primaryProjection T (j : F4[X])
              (sl6End F4 g w - w) ∈ (T).fixedSubmodule := by
            change primaryProjection T (j : F4[X])
              (sl6End F4 g w - w) ∈ (sl6End F4 (coordBlock45 A0)).fixedSubmodule
            rw [sl6End_fixedSubmodule_eq_primaryComponent]
            exact hcomp
          have hfixvec : T (primaryProjection T (j : F4[X])
              (sl6End F4 g w - w)) = primaryProjection T (j : F4[X])
                (sl6End F4 g w - w) :=
            LinearMap.mem_fixedSubmodule_iff.mp hzmem
          rw [LinearMap.sub_apply, hfixvec]
          simp
        · have hprojmem : primaryProjection T (j : F4[X]) w ∈ primaryComponent T (j : F4[X]) :=
            primaryProjection_mem hsq j.2 w
          have hfixproj : sl6End F4 g (primaryProjection T (j : F4[X]) w) =
              primaryProjection T (j : F4[X]) w :=
            hgfix (j : F4[X]) j.2 hj (primaryProjection T (j : F4[X]) w) hprojmem
          have hzero : primaryProjection T (j : F4[X])
              (sl6End F4 g w - w) = 0 := by
            rw [map_sub]
            change ((primaryProjection T (j : F4[X])) * (sl6End F4 g)) w -
              (primaryProjection T (j : F4[X])) w = 0
            rw [← hprojg.eq]
            change (sl6End F4 g) ((primaryProjection T (j : F4[X])) w) -
              (primaryProjection T (j : F4[X])) w = 0
            rw [hfixproj, sub_self]
          rw [hzero, map_zero]
      exact congrFun hprojzero x
    change z = 0
    simpa using hz
  calc sl6End F4 g v = sl6End F4 g ((T - 1) w) := by rw [hw]
    _ = (T - 1) (sl6End F4 g w) := by
        rw [LinearMap.sub_apply, map_sub, LinearMap.sub_apply]
        congr 1
        have h := congrArg (fun f : Module.End F4 (Fin 6 → F4) => f w) hgcomm.eq
        simpa [Module.End.mul_apply] using h
    _ = (T - 1) w := by
        have h := hkill
        rw [map_sub] at h
        exact sub_eq_zero.mp h
    _ = v := hw


private theorem gEnd_preserves_firstCoord (g : SL6F4) (A0 : SL2F4) (hAord : orderOf A0 = 5)
    (hA1 : A0 ≠ 1)
    (hgcomm : Commute (sl6End F4 g) (sl6End F4 (coordBlock45 A0)))
    {v : Fin 6 → F4} (hv : v ∈ firstCoord) :
    sl6End F4 g v ∈ firstCoord := by
  let T := sl6End F4 (coordBlock45 A0)
  have hvcomp : v ∈ primaryComponent T (X - 1) := by
    rw [primaryComponent_eq_firstCoord A0 hAord hA1]
    exact hv
  have hvfix : T v = v := by
    have h := mem_primaryComponent.mp hvcomp
    have h' : T v - v = 0 := by simpa [map_sub, aeval_X, map_one] using h
    exact sub_eq_zero.mp h'
  have hgvfix : T (sl6End F4 g v) = sl6End F4 g v := by
    have hc := congrArg (fun f : Module.End F4 (Fin 6 → F4) => f v) hgcomm.eq
    rw [Module.End.mul_apply, Module.End.mul_apply, hvfix] at hc
    exact hc.symm
  rw [← primaryComponent_eq_firstCoord A0 hAord hA1]
  rw [mem_primaryComponent]
  simpa [map_sub, aeval_X, map_one] using sub_eq_zero.mpr hgvfix


private noncomputable def gFirstLin (g : SL6F4)
    (hgpres : ∀ v ∈ firstCoord, sl6End F4 g v ∈ firstCoord) :
    (Fin 4 → F4) →ₗ[F4] (Fin 4 → F4) :=
  (firstCoordEquiv : firstCoord →ₗ[F4] (Fin 4 → F4)).comp
    ((sl6End F4 g).restrict (p := firstCoord) (q := firstCoord) hgpres |>.comp
      ((firstCoordEquiv.symm : (Fin 4 → F4) →ₗ[F4] firstCoord)))

private noncomputable def gFirstMat (g : SL6F4)
    (hgpres : ∀ v ∈ firstCoord, sl6End F4 g v ∈ firstCoord) :
    Matrix (Fin 4) (Fin 4) F4 :=
  LinearMap.toMatrix' (gFirstLin g hgpres)

private theorem gFirstLin_apply (g : SL6F4)
    (hgpres : ∀ v ∈ firstCoord, sl6End F4 g v ∈ firstCoord) (x : Fin 4 → F4) :
    gFirstLin g hgpres x =
      firstCoordEquiv ⟨sl6End F4 g (firstCoordEquiv.symm x),
        hgpres _ (firstCoordEquiv.symm x).2⟩ := by
  rfl

private theorem split46_gEnd_first (g : SL6F4)
    (hgpres : ∀ v ∈ firstCoord, sl6End F4 g v ∈ firstCoord) (x : Fin 4 → F4) :
    split46 (sl6End F4 g (split46.symm (x, 0))) =
      (gFirstLin g hgpres x, 0) := by
  have hmem : sl6End F4 g (firstCoordEquiv.symm x) ∈ firstCoord :=
    hgpres _ (firstCoordEquiv.symm x).2
  have hv : split46.symm (x, 0) = (firstCoordEquiv.symm x : Fin 6 → F4) := by
    apply split46.injective
    simp [firstCoordEquiv]
  rw [hv]
  apply Prod.ext
  · rw [show (split46 (sl6End F4 g (firstCoordEquiv.symm x))).1 =
      firstCoordEquiv ⟨sl6End F4 g (firstCoordEquiv.symm x), hmem⟩ from rfl]
    rw [gFirstLin_apply]
  · rw [show (split46 (sl6End F4 g (firstCoordEquiv.symm x))).2 = 0 from
      mem_firstCoord.mp hmem]

private theorem split46_gEnd_last (g : SL6F4) (hgfixlast : ∀ v ∈ lastCoord, sl6End F4 g v = v)
    (y : Fin 2 → F4) :
    split46 (sl6End F4 g (split46.symm (0, y))) = (0, y) := by
  have hmem : split46.symm (0, y) ∈ lastCoord := mem_lastCoord.mpr (by simp)
  rw [hgfixlast _ hmem]
  simp

private theorem split46_gEnd_block (g : SL6F4)
    (hgpres : ∀ v ∈ firstCoord, sl6End F4 g v ∈ firstCoord)
    (hgfixlast : ∀ v ∈ lastCoord, sl6End F4 g v = v) (v : Fin 6 → F4) :
    split46 (sl6End F4 g v) =
      ((gFirstMat g hgpres).mulVec (split46 v).1, (split46 v).2) := by
  generalize hxy : split46 v = p at *
  obtain ⟨x, y⟩ := p
  have hv : v = split46.symm (x, y) := by
    rw [← hxy]
    exact (split46.symm_apply_apply v).symm
  rw [hv]
  have hdecomp : split46.symm (x, y) =
      split46.symm (x, 0) + split46.symm (0, y) := by
    ext k
    rcases h : e46.symm k with i | j <;> simp [split46, h]
  rw [hdecomp, map_add, map_add, split46_gEnd_first g hgpres x,
    split46_gEnd_last g hgfixlast y]
  apply Prod.ext
  · funext i
    have hx : x = ∑ j : Fin 4, x j • Pi.single j (1 : F4) := by
      ext k
      simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hx]
    rw [map_sum]
    simp [gFirstMat, Matrix.mulVec, Matrix.toLin'_toMatrix', Finset.sum_apply,
      dotProduct, mul_comm]
  · simp


theorem blockFour_injective : Function.Injective (blockFour (K := F4)) := by
  intro A B hAB
  apply Subtype.ext
  ext i j
  have hmat : blockFourMat (A : Matrix (Fin 4) (Fin 4) F4) =
      blockFourMat (B : Matrix (Fin 4) (Fin 4) F4) := by
    simpa [coe_blockFour] using congrArg Subtype.val hAB
  have hentry := congrFun (congrFun hmat (e46 (Sum.inl i))) (e46 (Sum.inl j))
  rw [blockFourMat_apply, blockFourMat_apply, fromBlocks_apply₁₁, fromBlocks_apply₁₁] at hentry
  exact hentry

theorem natCard_blockFour_range :
    Nat.card (Set.range (blockFour (K := F4))) =
      Nat.card (Matrix.SpecialLinearGroup (Fin 4) F4) := by
  have h := Nat.card_range_of_injective (blockFour_injective)
  exact h


private theorem gFirstMat_mulVec (g : SL6F4)
    (hgpres : ∀ v ∈ firstCoord, sl6End F4 g v ∈ firstCoord) (x : Fin 4 → F4) :
    (gFirstMat g hgpres).mulVec x = gFirstLin g hgpres x := by
  simpa [gFirstMat] using LinearMap.toMatrix'_mulVec (gFirstLin g hgpres) x

private theorem split46_conj_gEnd_block (g : SL6F4)
    (hgpres : ∀ v ∈ firstCoord, sl6End F4 g v ∈ firstCoord)
    (hgfixlast : ∀ v ∈ lastCoord, sl6End F4 g v = v) :
    split46.conj (sl6End F4 g) =
      (gFirstLin g hgpres).prodMap (1 : Module.End F4 (Fin 2 → F4)) := by
  apply LinearMap.ext
  intro v
  rw [LinearEquiv.conj_apply_apply, LinearMap.prodMap_apply]
  have h := split46_gEnd_block g hgpres hgfixlast (split46.symm v)
  rw [h]
  simp [gFirstMat_mulVec]

private theorem gFirstLin_det_one (g : SL6F4)
    (hgpres : ∀ v ∈ firstCoord, sl6End F4 g v ∈ firstCoord)
    (hgfixlast : ∀ v ∈ lastCoord, sl6End F4 g v = v) :
    LinearMap.det (gFirstLin g hgpres) = 1 := by
  have hdetg : LinearMap.det (sl6End F4 g) = 1 := by
    rw [sl6End, coe_slGL, LinearMap.det_toLin']
    exact g.2
  have hconj := LinearMap.det_conj (sl6End F4 g) split46
  change LinearMap.det (split46.conj (sl6End F4 g)) = LinearMap.det (sl6End F4 g) at hconj
  rw [split46_conj_gEnd_block g hgpres hgfixlast] at hconj
  rw [LinearMap.det_prodMap] at hconj
  simpa [hdetg] using hconj


private noncomputable def gFirstSL (g : SL6F4)
    (hgpres : ∀ v ∈ firstCoord, sl6End F4 g v ∈ firstCoord)
    (hgfixlast : ∀ v ∈ lastCoord, sl6End F4 g v = v) : Matrix.SpecialLinearGroup (Fin 4) F4 :=
  ⟨gFirstMat g hgpres, by
    rw [gFirstMat, LinearMap.det_toMatrix']
    exact gFirstLin_det_one g hgpres hgfixlast⟩

private theorem g_eq_blockFour_gFirst (g : SL6F4)
    (hgpres : ∀ v ∈ firstCoord, sl6End F4 g v ∈ firstCoord)
    (hgfixlast : ∀ v ∈ lastCoord, sl6End F4 g v = v) :
    g = blockFour (K := F4) (gFirstSL g hgpres hgfixlast) := by
  apply slGL_injective
  apply Units.ext
  apply LinearMap.ext
  intro v
  apply split46.injective
  change split46 (sl6End F4 g v) = split46 (sl6End F4 (blockFour (K := F4) (gFirstSL g hgpres hgfixlast)) v)
  rw [split46_gEnd_block g hgpres hgfixlast v]
  rw [show sl6End F4 (blockFour (K := F4) (gFirstSL g hgpres hgfixlast)) v =
      (Matrix.toLin' (blockFour (K := F4) (gFirstSL g hgpres hgfixlast))) v by
    rw [sl6End, coe_slGL]]
  rw [split46_blockFour_apply_arbitrary]
  simp [gFirstSL]


theorem B_le_blockFour_range (A0 : SL2F4) (hAord : orderOf A0 = 5) (hA1 : A0 ≠ 1) :
    (linearSpecialBlock (slGL 6 F4 (coordBlock45 A0)) (X - 1)).comap (slGL 6 F4) ≤
      (blockFour (K := F4)).range := by
  intro g hgB
  have hg1 := Subgroup.mem_comap.mp hgB
  have hgcomm : Commute (sl6End F4 g) (sl6End F4 (coordBlock45 A0)) := by
    have := CFSG.RankThree.PartOne.KCUnitary.mem_gl_centralizer.mp hg1.1
    simpa [sl6End] using this
  have hgpres : ∀ v ∈ firstCoord, sl6End F4 g v ∈ firstCoord := by
    intro v hv
    exact gEnd_preserves_firstCoord g A0 hAord hA1 hgcomm hv
  have hgfixlast := gEnd_fixes_lastCoord g A0 hAord hA1 hgB
  refine MonoidHom.mem_range.mpr ⟨gFirstSL g hgpres hgfixlast, ?_⟩
  exact (g_eq_blockFour_gFirst g hgpres hgfixlast).symm

theorem blockFour_range_eq_comap (A0 : SL2F4) (hAord : orderOf A0 = 5) (hA1 : A0 ≠ 1) :
    (blockFour (K := F4)).range =
      (linearSpecialBlock (slGL 6 F4 (coordBlock45 A0)) (X - 1)).comap (slGL 6 F4) := by
  have hle := B_le_blockFour_range A0 hAord hA1
  have hcardB := natCard_linearSpecialBlock_comap A0 hAord hA1
  have hcardR := natCard_blockFour_range
  have hcardR' : Nat.card ↥(blockFour (K := F4)).range =
      Nat.card (Matrix.SpecialLinearGroup (Fin 4) F4) := hcardR
  have hcardB' : Nat.card ↥((linearSpecialBlock (slGL 6 F4 (coordBlock45 A0)) (X - 1)).comap
      (slGL 6 F4)) = Nat.card (Matrix.SpecialLinearGroup (Fin 4) F4) := by
    simpa using hcardB
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcardR', hcardB'])).symm


theorem blockFour_range_eq_comap_of_mem_coordT45 {a : SL6F4}
    (ha : a ∈ coordT45) (haord : orderOf a = 5) :
    (CFSG.SeitzReduction.E6Pilot.blockFour (K := F4)).range =
      (CFSG.RankThree.CALinearPrimary.linearSpecialBlock
        (CFSG.RankThree.CALinearPrimary.slGL 6 F4 a)
        (Polynomial.X - 1 : F4[X])).comap
        (CFSG.RankThree.CALinearPrimary.slGL 6 F4) := by
  obtain ⟨A0, rfl⟩ := exists_coordBlock45_of_mem_coordT45 ha
  have hAord : orderOf A0 = 5 := by
    rw [← orderOf_coordBlock45 A0]
    exact haord
  have hA1 : A0 ≠ 1 := by
    intro hA1
    rw [hA1] at haord
    simp at haord
  exact blockFour_range_eq_comap A0 hAord hA1


end

end CFSG.StandardType.N2KCoordinate

namespace CFSG.StandardType

open CFSG.StandardType.N2KCoordinate

local notation "SL4F4" => Matrix.SpecialLinearGroup (Fin 4) F4
open CFSG.SeitzReduction.E6Pilot
open CFSG.RankThree.CALinearPrimary


private theorem exists_literal_packet_T45
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G}
    {Rd Ra : Prop} (hR : GGSecFiveRestGen 5 B Bs x L D J Rd Ra)
    (hNbr : GGNbr 5 B x D J y K)
    (hL : GGCentralImage .POmegaMinus 4 2 L)
    (hK : GGCentralImage .PSL 6 2 K) :
    ∃ ψ : SL6F4 →* K,
      ∃ rho : Bs →* SL6F4,
        Function.Surjective ψ ∧
        ψ.ker ≤ Subgroup.center SL6F4 ∧
        (∀ b : Bs, MulAut.conj (ψ (rho b)) =
          (K.normalizerMonoidHom.comp
            (Subgroup.inclusion (ggF4N2_Bs_le_normalizer_K hR hNbr hL))) b) ∧
        (∀ (b : Bs) (k : K),
          ψ (rho b) * k * (ψ (rho b))⁻¹ =
            (K.normalizerMonoidHom.comp
              (Subgroup.inclusion (ggF4N2_Bs_le_normalizer_K hR hNbr hL))) b k) ∧
        (∀ b : Bs, (rho b) ^ 5 = 1) ∧
        rho.ker = (Subgroup.zpowers y).subgroupOf Bs ∧
        Nat.card rho.range = 5 ^ 3 ∧
        (K.subtype.comp (ψ.comp rho)).range = Bs ⊓ K ∧
        (∃ Q : Sylow 5 SL6F4, (Q : Subgroup SL6F4) = rho.range) ∧
        rho.range = coordinateTorus ∧
        (∀ hxBs : x ∈ Bs, rho ⟨x, hxBs⟩ ∈ coordT45) := by
  classical
  obtain ⟨hxBs, hxnot, -, -, -, -⟩ := ggF4N2_x_data hR hNbr
  obtain ⟨ψ, rho, hSurj, hKer, hConj, hPoint, hPow, hRhoKer, hRhoCard,
    hRange, hQ, hTorus⟩ := exists_literal_coordinate_torus_data hR hNbr hL hK
  have hfix : sl6FixedMultiplicity F4 (rho ⟨x, hxBs⟩) = 4 :=
    ggF4N2J_fixedMultiplicity_of_actual_lift hR hNbr hL hK ψ rho hSurj hKer
      hPoint hPow hRhoKer hxBs
  have hane : rho ⟨x, hxBs⟩ ≠ 1 := by
    intro h1
    have hxker : (⟨x, hxBs⟩ : Bs) ∈ rho.ker := MonoidHom.mem_ker.mpr h1
    rw [hRhoKer] at hxker
    exact hxnot (Subgroup.mem_subgroupOf.mp hxker)
  have ha5 : orderOf (rho ⟨x, hxBs⟩) = 5 :=
    orderOf_eq_prime (hPow ⟨x, hxBs⟩) hane
  have hmemT : rho ⟨x, hxBs⟩ ∈ coordinateTorus := by
    have hmemRange : rho ⟨x, hxBs⟩ ∈ rho.range :=
      ⟨⟨x, hxBs⟩, rfl⟩
    simpa [hTorus] using hmemRange
  have hsupp := coordinateTorus_support_one hmemT ha5 hfix
  obtain ⟨g, hgTorus, hg45⟩ := exists_conj_mem_coordT45 (rho ⟨x, hxBs⟩) hsupp
  let α : MulAut SL6F4 := MulAut.conj g
  let ψc : SL6F4 →* K := ψ.comp α.symm.toMonoidHom
  let rhoc : Bs →* SL6F4 := α.toMonoidHom.comp rho
  have hcomp : ψc.comp rhoc = ψ.comp rho := by
    ext b
    simp only [MonoidHom.comp_apply, ψc, rhoc, MulEquiv.coe_toMonoidHom]
    rw [MulEquiv.symm_apply_apply]
  have hcompPoint (b : Bs) : ψc (rhoc b) = ψ (rho b) :=
    congrArg (fun f : Bs →* K => f b) hcomp
  have hSurjc : Function.Surjective ψc := by
    intro k
    obtain ⟨a, ha⟩ := hSurj k
    refine ⟨α a, ?_⟩
    simpa [ψc] using ha
  have hKerc : ψc.ker ≤ Subgroup.center SL6F4 := by
    intro a ha
    have hz : α.symm a ∈ Subgroup.center SL6F4 := by
      apply hKer
      change ψ (α.symm a) = 1
      exact ha
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro b
    have h := congrArg α (hz (α.symm b))
    simpa only [map_mul, α.apply_symm_apply] using h
  have hConjc : ∀ b : Bs, MulAut.conj (ψc (rhoc b)) =
      (K.normalizerMonoidHom.comp
        (Subgroup.inclusion (ggF4N2_Bs_le_normalizer_K hR hNbr hL))) b := by
    intro b
    rw [hcompPoint]
    exact hConj b
  have hPointc : ∀ (b : Bs) (k : K),
      ψc (rhoc b) * k * (ψc (rhoc b))⁻¹ =
        (K.normalizerMonoidHom.comp
          (Subgroup.inclusion (ggF4N2_Bs_le_normalizer_K hR hNbr hL))) b k := by
    intro b k
    rw [hcompPoint]
    exact hPoint b k
  have hPowc : ∀ b : Bs, (rhoc b) ^ 5 = 1 := by
    intro b
    change (α (rho b)) ^ 5 = 1
    rw [← map_pow, hPow b, map_one]
  have hRhoKerc : rhoc.ker = (Subgroup.zpowers y).subgroupOf Bs := by
    rw [← hRhoKer]
    ext b
    change α (rho b) = 1 ↔ rho b = 1
    constructor
    · intro h
      apply α.injective
      simpa using h
    · intro h
      rw [h, map_one]
  have hrange : rhoc.range = coordinateTorus := by
    change (α.toMonoidHom.comp rho).range = coordinateTorus
    rw [MonoidHom.range_comp, hTorus, hgTorus]
  have hCardc : Nat.card rhoc.range = 5 ^ 3 := by
    rw [hrange]
    exact coordinateTorus_card
  have hRangec : (K.subtype.comp (ψc.comp rhoc)).range = Bs ⊓ K := by
    rw [hcomp]
    exact hRange
  have hQc : ∃ Q : Sylow 5 SL6F4, (Q : Subgroup SL6F4) = rhoc.range :=
    ⟨coordinateSylow, coordinateSylow_coe.trans hrange.symm⟩
  refine ⟨ψc, rhoc, hSurjc, hKerc, hConjc, hPointc, hPowc, hRhoKerc,
    hCardc, hRangec, hQc, hrange, ?_⟩
  intro hxBs'
  change α (rho ⟨x, hxBs'⟩) ∈ coordT45
  simpa [α, MulAut.conj_apply] using hg45


private theorem exists_eJ_of_literal_range
    {G : Type} [Group G] [Finite G] {J K : Subgroup G}
    (ψ : SL6F4 →* K)
    (hJeq : J = blockFour.range.map (K.subtype.comp ψ))
    (hcardJ : Nat.card ↥J = Nat.card SL4F4) :
    ∃ eJ : ↥J ≃* SL4F4,
      ∀ g : SL4F4, (ψ (blockFour (K := F4) g) : G) = (eJ.symm g : G) := by
  classical
  let Φ : SL4F4 →* G := K.subtype.comp (ψ.comp (blockFour (K := F4)))
  have hΦrange : Φ.range = J := by
    change ((K.subtype.comp ψ).comp (blockFour (K := F4))).range = J
    rw [MonoidHom.range_comp]
    exact hJeq.symm
  let Ψ : SL4F4 →* ↥J := Φ.codRestrict J fun g => by
    rw [← hΦrange]
    exact ⟨g, rfl⟩
  have hsurj : Function.Surjective Ψ := by
    intro j
    have hj : (j : G) ∈ Φ.range := by
      rw [hΦrange]
      exact j.2
    rw [MonoidHom.mem_range] at hj
    obtain ⟨g, hg⟩ := hj
    exact ⟨g, Subtype.ext hg⟩
  have hbij : Function.Bijective Ψ :=
    hsurj.bijective_of_nat_card_le (by rw [hcardJ])
  let eSL : SL4F4 ≃* ↥J := MulEquiv.ofBijective Ψ hbij
  let eJ : ↥J ≃* SL4F4 := eSL.symm
  refine ⟨eJ, ?_⟩
  intro g
  rfl


private theorem J_eq_literal_range_of_blockEq
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G}
    {Rd Ra : Prop} (hR : GGSecFiveRestGen 5 B Bs x L D J Rd Ra)
    (hNbr : GGNbr 5 B x D J y K)
    (hL : GGCentralImage .POmegaMinus 4 2 L)
    (hK : GGCentralImage .PSL 6 2 K)
    (ψ : SL6F4 →* K) (rho : Bs →* SL6F4)
    (hSurj : Function.Surjective ψ)
    (hKer : ψ.ker ≤ Subgroup.center SL6F4)
    (hPoint : ∀ (b : Bs) (k : K), ψ (rho b) * k * (ψ (rho b))⁻¹ =
      (K.normalizerMonoidHom.comp
        (Subgroup.inclusion (ggF4N2_Bs_le_normalizer_K hR hNbr hL))) b k)
    (hPow : ∀ b : Bs, (rho b) ^ 5 = 1)
    (hRhoKer : rho.ker = (Subgroup.zpowers y).subgroupOf Bs)
    {hxBs : x ∈ Bs}
    (hblock : blockFour.range =
      (linearSpecialBlock (slGL 6 F4 (rho ⟨x, hxBs⟩))
        (Polynomial.X - 1)).comap (slGL 6 F4)) :
    J = blockFour.range.map (K.subtype.comp ψ) := by
  classical
  have hJK : J ≤ K := ggF4N2J_le_psl6_neighbor hR hNbr hL hK
  have hfixRange := ggF4N2J_fixedBlockRange_of_actual_lift hR hNbr hL hK
    ψ rho hSurj hKer hPoint hPow hRhoKer hxBs
  have hJmap := congrArg (fun S : Subgroup K => S.map K.subtype) hfixRange
  rw [Subgroup.map_subgroupOf_eq_of_le hJK] at hJmap
  simpa [hblock, Subgroup.map_map] using hJmap


private theorem card_J_eq_card_SL4F4
    {G : Type} [Group G] {J : Subgroup G} {F0 : Type} [Field F0] [Finite F0]
    (e0 : ↥J ≃* Matrix.SpecialLinearGroup (Fin 4) F0)
    (hF0 : Nat.card F0 = 4) :
    Nat.card ↥J = Nat.card SL4F4 := by
  classical
  haveI : Fintype F0 := Fintype.ofFinite F0
  haveI : Fintype F4 := Fintype.ofFinite F4
  have hF4 : Nat.card F4 = 4 := by
    simpa using GaloisField.card 2 2 (by norm_num)
  have hF0' : Fintype.card F0 = 4 := by
    simpa [Nat.card_eq_fintype_card] using hF0
  have hF4' : Fintype.card F4 = 4 := by
    simpa [Nat.card_eq_fintype_card] using hF4
  rw [Nat.card_congr e0.toEquiv]
  rw [Matrix.card_SL_field (𝔽 := F0) 4, Matrix.card_SL_field (𝔽 := F4) 4,
    hF0', hF4']


private theorem exists_eJ_literal_of_packet
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G}
    {Rd Ra : Prop} (hR : GGSecFiveRestGen 5 B Bs x L D J Rd Ra)
    (hNbr : GGNbr 5 B x D J y K)
    (hL : GGCentralImage .POmegaMinus 4 2 L)
    (hK : GGCentralImage .PSL 6 2 K)
    (ψ : SL6F4 →* K) (rho : Bs →* SL6F4)
    (hSurj : Function.Surjective ψ)
    (hKer : ψ.ker ≤ Subgroup.center SL6F4)
    (hPoint : ∀ (b : Bs) (k : K), ψ (rho b) * k * (ψ (rho b))⁻¹ =
      (K.normalizerMonoidHom.comp
        (Subgroup.inclusion (ggF4N2_Bs_le_normalizer_K hR hNbr hL))) b k)
    (hPow : ∀ b : Bs, (rho b) ^ 5 = 1)
    (hRhoKer : rho.ker = (Subgroup.zpowers y).subgroupOf Bs)
    {hxBs : x ∈ Bs}
    (hblock : blockFour.range =
      (linearSpecialBlock (slGL 6 F4 (rho ⟨x, hxBs⟩))
        (Polynomial.X - 1)).comap (slGL 6 F4))
    {F0 : Type} [Field F0] [Finite F0]
    (e0 : ↥J ≃* Matrix.SpecialLinearGroup (Fin 4) F0)
    (hF0 : Nat.card F0 = 4) :
    ∃ eJ : ↥J ≃* SL4F4,
      ∀ g : SL4F4, (ψ (blockFour (K := F4) g) : G) = (eJ.symm g : G) := by
  classical
  have hJeq : J = blockFour.range.map (K.subtype.comp ψ) :=
    J_eq_literal_range_of_blockEq hR hNbr hL hK ψ rho hSurj hKer hPoint hPow
      hRhoKer (hxBs := hxBs) hblock
  have hcardJ : Nat.card ↥J = Nat.card SL4F4 :=
    card_J_eq_card_SL4F4 e0 hF0
  exact exists_eJ_of_literal_range ψ hJeq hcardJ


private theorem rootImage_eq_of_directChart
    {G : Type} [Group G] {J K : Subgroup G}
    {ψ : SL6F4 →* K} {eJ : ↥J ≃* SL4F4}
    (hchart : ∀ g : SL4F4, (ψ (blockFour (K := F4) g) : G) = (eJ.symm g : G)) :
    (rootR F4).map (K.subtype.comp (ψ.comp (blockFour (K := F4)))) =
      (rootR F4).map (J.subtype.comp eJ.symm.toMonoidHom) := by
  classical
  let chartHom : SL4F4 →* G := K.subtype.comp (ψ.comp (blockFour (K := F4)))
  let rootHom : SL4F4 →* G := J.subtype.comp eJ.symm.toMonoidHom
  have hhom : chartHom = rootHom := by
    apply MonoidHom.ext
    intro g
    exact hchart g
  rw [show (rootR F4).map (K.subtype.comp (ψ.comp (blockFour (K := F4)))) =
      (rootR F4).map chartHom from rfl]
  rw [hhom]


private theorem literal_eJ_and_root_of_packet
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G}
    {Rd Ra : Prop} (hR : GGSecFiveRestGen 5 B Bs x L D J Rd Ra)
    (hNbr : GGNbr 5 B x D J y K)
    (hL : GGCentralImage .POmegaMinus 4 2 L)
    (hK : GGCentralImage .PSL 6 2 K)
    (ψ : SL6F4 →* K) (rho : Bs →* SL6F4)
    (hSurj : Function.Surjective ψ)
    (hKer : ψ.ker ≤ Subgroup.center SL6F4)
    (hPoint : ∀ (b : Bs) (k : K), ψ (rho b) * k * (ψ (rho b))⁻¹ =
      (K.normalizerMonoidHom.comp
        (Subgroup.inclusion (ggF4N2_Bs_le_normalizer_K hR hNbr hL))) b k)
    (hPow : ∀ b : Bs, (rho b) ^ 5 = 1)
    (hRhoKer : rho.ker = (Subgroup.zpowers y).subgroupOf Bs)
    {hxBs : x ∈ Bs}
    (hblock : blockFour.range =
      (linearSpecialBlock (slGL 6 F4 (rho ⟨x, hxBs⟩))
        (Polynomial.X - 1)).comap (slGL 6 F4))
    {F0 : Type} [Field F0] [Finite F0]
    (e0 : ↥J ≃* Matrix.SpecialLinearGroup (Fin 4) F0)
    (hF0 : Nat.card F0 = 4) :
    ∃ eJ : ↥J ≃* SL4F4,
      (∀ g : SL4F4, (ψ (blockFour (K := F4) g) : G) = (eJ.symm g : G)) ∧
      (rootR F4).map (K.subtype.comp (ψ.comp (blockFour (K := F4)))) =
        (rootR F4).map (J.subtype.comp eJ.symm.toMonoidHom) := by
  classical
  obtain ⟨eJ, hchart⟩ := exists_eJ_literal_of_packet hR hNbr hL hK ψ rho
    hSurj hKer hPoint hPow hRhoKer (hxBs := hxBs) hblock e0 hF0
  exact ⟨eJ, hchart, rootImage_eq_of_directChart hchart⟩


theorem ggF4N2K_originalLiteralChart_of_original_data
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G}
    {Rd Ra : Prop} (hR : GGSecFiveRestGen 5 B Bs x L D J Rd Ra)
    (hNbr : GGNbr 5 B x D J y K)
    (hL : GGCentralImage .POmegaMinus 4 2 L)
    (hK : GGCentralImage .PSL 6 2 K) :
    ∃ ψ : SL6F4 →* K,
      ∃ rho : Bs →* SL6F4,
        Function.Surjective ψ ∧
        ψ.ker ≤ Subgroup.center SL6F4 ∧
        (∀ b : Bs, MulAut.conj (ψ (rho b)) =
          (K.normalizerMonoidHom.comp
            (Subgroup.inclusion (ggF4N2_Bs_le_normalizer_K hR hNbr hL))) b) ∧
        (∀ (b : Bs) (k : K),
          ψ (rho b) * k * (ψ (rho b))⁻¹ =
            (K.normalizerMonoidHom.comp
              (Subgroup.inclusion (ggF4N2_Bs_le_normalizer_K hR hNbr hL))) b k) ∧
        (∀ b : Bs, (rho b) ^ 5 = 1) ∧
        rho.ker = (Subgroup.zpowers y).subgroupOf Bs ∧
        Nat.card rho.range = 5 ^ 3 ∧
        (K.subtype.comp (ψ.comp rho)).range = Bs ⊓ K ∧
        (∃ Q : Sylow 5 SL6F4, (Q : Subgroup SL6F4) = rho.range) ∧
        rho.range = coordinateTorus ∧
        rho ⟨x, (ggF4N2_x_data hR hNbr).1⟩ ∈ coordT45 ∧
        J = blockFour.range.map (K.subtype.comp ψ) ∧
        (∃ eJ : ↥J ≃* SL4F4,
          (∀ g : SL4F4,
            (ψ (blockFour (K := F4) g) : G) = (eJ.symm g : G)) ∧
          (rootR F4).map (K.subtype.comp (ψ.comp (blockFour (K := F4)))) =
            (rootR F4).map (J.subtype.comp eJ.symm.toMonoidHom)) := by
  classical
  obtain ⟨hxBs, hxnot, -, -, -, -⟩ := ggF4N2_x_data hR hNbr
  obtain ⟨ψ, rho, hSurj, hKer, hConj, hPoint, hPow, hRhoKer, hCard,
    hRangeK, hQ, hTorus, hT45⟩ := exists_literal_packet_T45 hR hNbr hL hK
  have hane : rho ⟨x, hxBs⟩ ≠ 1 := by
    intro h1
    have hxker : (⟨x, hxBs⟩ : Bs) ∈ rho.ker := MonoidHom.mem_ker.mpr h1
    rw [hRhoKer] at hxker
    exact hxnot (Subgroup.mem_subgroupOf.mp hxker)
  have haord : orderOf (rho ⟨x, hxBs⟩) = 5 :=
    orderOf_eq_prime (hPow ⟨x, hxBs⟩) hane
  have hblock : blockFour.range =
      (linearSpecialBlock (slGL 6 F4 (rho ⟨x, hxBs⟩))
        (Polynomial.X - 1)).comap (slGL 6 F4) :=
    blockFour_range_eq_comap_of_mem_coordT45 (hT45 hxBs) haord
  obtain ⟨-, hRec⟩ := ggF4N2J_original_mixed_recognition hR hNbr hL hK
  obtain ⟨⟨F0, hField, hFinite, hChar, hF0, ⟨e0⟩⟩, -⟩ := hRec
  letI : Field F0 := hField
  letI : Finite F0 := hFinite
  obtain ⟨eJ, hchart, hroot⟩ :=
    literal_eJ_and_root_of_packet hR hNbr hL hK ψ rho hSurj hKer hPoint
      hPow hRhoKer (hxBs := hxBs) hblock e0 hF0
  have hJeq : J = blockFour.range.map (K.subtype.comp ψ) :=
    J_eq_literal_range_of_blockEq hR hNbr hL hK ψ rho hSurj hKer hPoint
      hPow hRhoKer (hxBs := hxBs) hblock
  exact ⟨ψ, rho, hSurj, hKer, hConj, hPoint, hPow, hRhoKer, hCard,
    hRangeK, hQ, hTorus, hT45 (ggF4N2_x_data hR hNbr).1, hJeq, eJ, hchart, hroot⟩


theorem ggF4N2K_exists_original_inverter_D_action
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G}
    {Rd Ra : Prop} (hR : GGSecFiveRestGen 5 B Bs x L D J Rd Ra)
    (hNbr : GGNbr 5 B x D J y K)
    (hL : GGCentralImage .POmegaMinus 4 2 L)
    (hK : GGCentralImage .PSL 6 2 K) :
    ∃ t : G, t ∈ K ∧ t ∈ Subgroup.normalizer (Bs : Set G) ∧
      t ∈ Subgroup.centralizer (J : Set G) ∧
      t ∈ Subgroup.normalizer (D : Set G) ∧
      (MulAut.conj t) y = y ∧
      (∀ z ∈ Bs, (MulAut.conj t) ((MulAut.conj t) z) = z) ∧
      ∃ a : G, a ∈ D ∧ orderOf a = 5 ∧
        (MulAut.conj t) a = a⁻¹ ∧ (MulAut.conj t) a ≠ a := by
  obtain ⟨ψ, rho, -, hKer, -, -, -, -, -, hRangeK, -, hTorus, -, hJ, -⟩ :=
    ggF4N2K_originalLiteralChart_of_original_data hR hNbr hL hK
  have hE := N2KCoordinate.original_torus_join_of_actual_lift
    hR hNbr hL hK ψ rho hRangeK hTorus
  have hyC : Subgroup.zpowers y ≤ Subgroup.centralizer (K : Set G) := by
    rw [← inf_centralizer_eq_zpowers_of_sHat hNbr.1]
    exact inf_le_right
  exact N2KCoordinate.exists_inverter_with_nontrivial_involutive_D_action ψ hKer
    hE hJ (hyC (Subgroup.mem_zpowers y)) (ggF4N2_D_eq_Bs_inf_centralizer_J hR hL)


theorem ggF4N2K_exists_original_inverter_orderTwo_on_D
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G}
    {Rd Ra : Prop} (hR : GGSecFiveRestGen 5 B Bs x L D J Rd Ra)
    (hNbr : GGNbr 5 B x D J y K)
    (hL : GGCentralImage .POmegaMinus 4 2 L)
    (hK : GGCentralImage .PSL 6 2 K) :
    ∃ t : G, t ∈ K ∧ t ∈ Subgroup.normalizer (Bs : Set G) ∧
      t ∈ Subgroup.centralizer (J : Set G) ∧
      ∃ htD : t ∈ Subgroup.normalizer (D : Set G),
        (MulAut.conj t) y = y ∧ orderOf (D.normalizerMonoidHom ⟨t, htD⟩) = 2 := by
  obtain ⟨t, htK, htBs, htJ, htD, hty, hfix, a, haD, -, -, hane⟩ :=
    ggF4N2K_exists_original_inverter_D_action hR hNbr hL hK
  let α : MulAut D := D.normalizerMonoidHom ⟨t, htD⟩
  have hα (d : D) : (α d : G) = (MulAut.conj t) (d : G) :=
    Subgroup.normalizerMonoidHom_apply_apply_coe D ⟨t, htD⟩ d
  have hDBs : D ≤ Bs := hR.1.2.2.1.1.trans hR.1.2.1.1
  have hpow : α ^ 2 = 1 := by
    apply MulEquiv.ext
    intro d
    apply Subtype.ext
    change (α (α d) : G) = (d : G)
    rw [hα, hα]
    exact hfix (d : G) (hDBs d.2)
  have hne : α ≠ 1 := by
    intro h
    apply hane
    have hh := hα ⟨a, haD⟩
    rw [h] at hh
    exact hh.symm
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ⟨t, htK, htBs, htJ, htD, hty, orderOf_eq_prime hpow hne⟩

theorem ggF4N2K_exists_original_inverter_reflection
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G}
    {Rd Ra : Prop} (hR : GGSecFiveRestGen 5 B Bs x L D J Rd Ra)
    (hNbr : GGNbr 5 B x D J y K)
    (hL : GGCentralImage .POmegaMinus 4 2 L)
    (hK : GGCentralImage .PSL 6 2 K) :
    ∃ t : G, t ∈ K ∧ ∃ htBs : t ∈ Subgroup.normalizer (Bs : Set G),
      t ∈ Subgroup.centralizer (J : Set G) ∧
      t ∈ Subgroup.normalizer (D : Set G) ∧
      (MulAut.conj t) y = y ∧
      ggConjAut Bs htBs ∈ ggAutomizer K Bs ∧
      GGIsReflection 5 (ggConjAut Bs htBs) ∧
      ggFixG Bs (ggConjAut Bs htBs) =
        Subgroup.zpowers y ⊔ (Bs ⊓ J) ∧
      Nat.card ↥(ggFixG Bs (ggConjAut Bs htBs)) = 125 ∧
      ∃ a : G, a ∈ D ∧ orderOf a = 5 ∧
        (MulAut.conj t) a = a⁻¹ ∧ (MulAut.conj t) a ≠ a := by
  classical
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨t, htK, htBs, htJ, htD, hty, hfix_sq, a, haD, ha5, _ha_inv, ha_ne⟩ :=
    ggF4N2K_exists_original_inverter_D_action hR hNbr hL hK
  obtain ⟨_, _, hyOrder, hDclosure, _, _⟩ :=
    ggF4N2_x_data hR hNbr
  have hcfg : GGConfig 5 B Bs x L D J := hR.1
  have hBsElem : CFSG.Open.IsElemAbelian 5 Bs := hcfg.2.1.2.1
  have hDeq : D = Bs ⊓ Subgroup.centralizer (J : Set G) :=
    ggF4N2_D_eq_Bs_inf_centralizer_J hR hL
  have hDBs : D ≤ Bs := by
    rw [hDeq]
    exact inf_le_left
  obtain ⟨-, hdisj, hInt25, -⟩ :=
    ggF4N2J_original_torus_split hR hNbr hL hK
  have hrank := ggF4N2Rank hR hL
  have hcardBs : Nat.card Bs = 625 := by
    have h := hrank.1
    norm_num at h ⊢
    exact h
  have hyD : y ∈ D := by
    rw [hDclosure]
    exact Subgroup.subset_closure (by simp)
  have hyBs : y ∈ Bs := hDBs hyD
  have hzD : Subgroup.zpowers y ≤ D := Subgroup.zpowers_le.mpr hyD
  have hzBs : Subgroup.zpowers y ≤ Bs := hzD.trans hDBs
  let τ : MulAut ↥Bs := ggConjAut Bs htBs
  have hcommJoin : ∀ a ∈ Subgroup.zpowers y, ∀ b ∈ Bs ⊓ J, a * b = b * a := by
    intro a ha b hb
    have haBs : a ∈ Bs := hzBs ha
    have hbBs : b ∈ Bs := hb.1
    have hcomm := hBsElem.1.is_comm.comm (⟨a, haBs⟩ : ↥Bs) (⟨b, hbBs⟩ : ↥Bs)
    exact congrArg (fun z : ↥Bs => (z : G)) hcomm
  have hdisjJoin : Subgroup.zpowers y ⊓ (Bs ⊓ J) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hzD : z ∈ D := hzD hz.1
    have hzJ : z ∈ J := hz.2.2
    have hzDJ : z ∈ D ⊓ J := ⟨hzD, hzJ⟩
    have hDJ : D ⊓ J = ⊥ := disjoint_iff.mp hdisj
    rwa [hDJ] at hzDJ
  have hcardJoin : Nat.card ↥(Subgroup.zpowers y ⊔ (Bs ⊓ J)) = 125 := by
    rw [CFSG.card_sup_eq_mul_of_commute (Subgroup.zpowers y) (Bs ⊓ J) hcommJoin hdisjJoin]
    have hy5 : Nat.card (Subgroup.zpowers y) = 5 := by
      rw [Nat.card_zpowers, hyOrder]
    have hInt25' : Nat.card ↥(Bs ⊓ J) = 25 := hInt25
    rw [hy5, hInt25']
  have hyFix : y ∈ ggFixG Bs τ := by
    refine ⟨⟨y, hyBs⟩, ?_, rfl⟩
    apply Subtype.ext
    rw [ggConjAut_apply]
    exact hty
  have hIntFix : Bs ⊓ J ≤ ggFixG Bs τ := by
    intro z hz
    refine ⟨⟨z, hz.1⟩, ?_, rfl⟩
    apply Subtype.ext
    rw [ggConjAut_apply]
    have hcomm : z * t = t * z :=
      (Subgroup.mem_centralizer_iff.mp htJ) z hz.2
    rw [← hcomm]
    group
  have hjoin_le : Subgroup.zpowers y ⊔ (Bs ⊓ J) ≤ ggFixG Bs τ :=
    sup_le (Subgroup.zpowers_le.mpr hyFix) hIntFix
  have hτ2 : τ ^ 2 = 1 := by
    apply MulEquiv.ext
    intro b
    apply Subtype.ext
    change ((τ (τ b) : ↥Bs) : G) = (b : G)
    rw [show τ = ggConjAut Bs htBs from rfl]
    rw [ggConjAut_apply, ggConjAut_apply]
    simpa [MulAut.conj_apply] using hfix_sq (b : G) b.2
  have haBs : a ∈ Bs := hDBs haD
  have ha_notFix : a ∉ ggFixG Bs τ := by
    intro haFix
    rcases (Subgroup.mem_map.mp haFix) with ⟨c, hc, hcb⟩
    have hcb' : c = ⟨a, haBs⟩ := Subtype.ext hcb
    have hfixa : τ ⟨a, haBs⟩ = ⟨a, haBs⟩ := by
      rw [← hcb']
      exact hc
    have hconj : (MulAut.conj t) a = a := by
      have := congrArg (fun b : ↥Bs => (b : G)) hfixa
      simpa [τ, ggConjAut_apply, MulAut.conj_apply] using this
    exact ha_ne hconj
  have hne : ggFixG Bs τ ≠ Bs := by
    intro h
    have haG : a ∈ ggFixG Bs τ := by
      rw [h]
      exact haBs
    exact ha_notFix haG
  have hfix_le : ggFixG Bs τ ≤ Bs := by
    rw [ggFixG]
    exact Subgroup.map_subtype_le _
  have hcardB_lower : 125 ≤ Nat.card ↥(ggFixG Bs τ) := by
    rw [← hcardJoin]
    exact Subgroup.card_le_of_le hjoin_le
  have hcard : Nat.card Bs ≤ 5 * Nat.card ↥(ggFixG Bs τ) := by
    rw [hcardBs]
    omega
  have hiff : ∀ b : ↥Bs, ((b : G) ∈ ggFixG Bs τ ↔ τ b = b) := by
    intro b
    constructor
    · intro hb
      rcases (Subgroup.mem_map.mp hb) with ⟨c, hc, hcb⟩
      have hcb' : c = b := Subtype.ext hcb
      rwa [hcb'] at hc
    · intro hb
      exact Subgroup.mem_map.mpr ⟨b, hb, rfl⟩
  have hrefl : GGIsReflection 5 τ :=
    isReflection_of_fix_iff_mem Nat.prime_five hfix_le hBsElem hcard hne hτ2 hiff
  have hBcard : Nat.card ↥(ggFixG Bs τ) = Nat.card {b : ↥Bs // τ b = b} := by
    rw [ggFixG, Subgroup.card_map_of_injective Bs.subtype_injective]
    rfl
  have hB125 : Nat.card ↥(ggFixG Bs τ) = 125 := by
    have h := hrefl.2
    rw [← hBcard, hcardBs] at h
    omega
  have hEq : ggFixG Bs τ = Subgroup.zpowers y ⊔ (Bs ⊓ J) := by
    symm
    exact Subgroup.eq_of_le_of_card_ge hjoin_le (by rw [hcardJoin, hB125])
  exact ⟨t, htK, htBs, htJ, htD, hty, ggConjAut_mem_ggAutomizer htK htBs,
    hrefl, hEq, hB125, a, haD, ha5, _ha_inv, ha_ne⟩


section InternalLine

open N2KCoordinate N2KComplementary
open CFSG.SeitzReduction.E6Pilot CFSG.SeitzReduction.LinearPilot


end InternalLine

section AmbientPower

open CFSG.SeitzReduction.E6Pilot
open CFSG.ComponentClassification.CatalogueBHigherLinearAction
open CFSG.ComponentClassification.CatalogueBGraphForm


end AmbientPower

end CFSG.StandardType


namespace CFSG.StandardType

open CFSG.StandardType.N2KComplementary
open CFSG.StandardType.N2KCoordinate


namespace N2KRootAction


open CFSG.StandardType
open CFSG.StandardType.N2KCoordinate
open CFSG.SeitzReduction.E6Pilot
open CFSG.SeitzReduction.LinearPilot
open CFSG.ClassicalGroups.SpecialLinear
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Assembly

abbrev F4 := N2KCoordinate.F4
abbrev SL6F4 := Matrix.SpecialLinearGroup (Fin 6) F4


end N2KRootAction


end CFSG.StandardType

public section
namespace CFSG.StandardType.N2KRootAction
open CFSG.StandardType CFSG.StandardType.N2KCoordinate CFSG.SeitzReduction.E6Pilot CFSG.ClassicalGroups.SpecialLinear CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.Assembly


end CFSG.StandardType.N2KRootAction


namespace CFSG.StandardType.N2F4LabelNative


open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.StandardType
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LieType.Chevalley.F4NativeNormalForm


section Outer


open CFSG.SeitzReduction.LinearPilot


end Outer

end CFSG.StandardType.N2F4LabelNative

noncomputable section

namespace CFSG.StandardType.N2F4NeighbourInner

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.StandardType
open CFSG.LieType.Chevalley


section NativeLowRankPosition
open CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.StandardType.F4ExplicitPos CFSG.StandardType.F4ExplicitPos.AmbientAction
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley


end NativeLowRankPosition

end CFSG.StandardType.N2F4NeighbourInner

end
