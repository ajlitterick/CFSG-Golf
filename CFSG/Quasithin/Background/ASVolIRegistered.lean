module

public import CFSG.Open.QuasithinH1NaturalModulesMilestoneDefs
public import CFSG.Quasithin.Background.F6CatDickson
public import CFSG.Quasithin.Background.JonesParshallSector
public import CFSG.Quasithin.H13.ModelsUnitary
public import CFSG.Quasithin.H13.ModelsLinear
public import CFSG.Quasithin.H13.ModelsSymplectic
public import CFSG.Quasithin.H13.ModelsG2
public import CFSG.Quasithin.H13.ModelsSporadic
public import CFSG.Quasithin.Background.SmithB42G2Id
public import CFSG.Quasithin.Recognition.ModelBridges
public import CFSG.GH74.Bender.Suzuki
public import CFSG.LieType.Steinberg.CentralExt.PSpMultiplier
public import CFSG.Alternating.Multipliers.Main
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.ProvedRows
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.M12CoverRow
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.J2CoverRow
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.J3CoverCert
import all CFSG.Blueprint.NativeSporadic
public import CFSG.Certificates.CentralKernel
public import CFSG.Certificates.CosetTableWalkC
public import CFSG.Certificates.FusionF2
public import CFSG.Certificates.WordSubgroupHom
public import CFSG.GH74.GLS.Classes
public import CFSG.GH74.Statements
public import CFSG.LieType.Multipliers.ProductKernel
public import CFSG.LieType.Multipliers.U42Bridge
public import CFSG.LieType.Multipliers.U43Action
public import CFSG.LieType.Multipliers.U43BridgeInputs
public import CFSG.LieType.Multipliers.U62Action
public import CFSG.LieType.Multipliers.U62Bridge
public import CFSG.LieType.Multipliers.U62Kernel
public import CFSG.LieType.Steinberg.CentralExt.PSL2Multiplier
public import CFSG.LocalAnalysis.AGLEmbedding.SporadicData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoProjectiveFormulas
public import CFSG.LocalAnalysis.ComponentClassification.GSLitInputs
public import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionQuaternion
public import CFSG.LocalAnalysis.ComponentClassification.TBLitCover
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeCheckBase
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeModel
public import CFSG.LocalAnalysis.EvenSmallLie.Sp6JCondition
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Milestones.CL_LIT_SQTK_simple_list
public import CFSG.Monster.B.Classical.PlaneAut
public import CFSG.Monster.B.TwoA.Amalgam.Data
public import CFSG.Monster.B.TwoA.Sp8.Par1
public import CFSG.Monster.B.TwoA.Unitary.LinThree
public import CFSG.Quasithin.Background.A1cA132Action
public import CFSG.Quasithin.Background.A1cA133Three
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.CTP.StrongPSylow
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.SporadicTable
public import CFSG.Sporadic.Presentation.Co2Base
public import CFSG.Sporadic.Presentation.Co2Cover
public import CFSG.Sporadic.Presentation.Co2Fusion
public import CFSG.Sporadic.Presentation.Co2FusionInputs
public import CFSG.Sporadic.Presentation.McLExactData
public import CFSG.Sporadic.Presentation.McLExactInputs
public import CFSG.Sporadic.Recognition.McLMultiplierMatrix
public import CFSG.Sporadic.Schreier.TitsOther
public import CFSG.Sporadic.SmallOddCore.CheckSpec
public import CFSG.YGroups.DCE.B433Check
public import Certificates.Certificate10005
public import Certificates.Certificate10006
public import Certificates.Certificate10007
public import Certificates.Certificate10008
public import Certificates.Certificate10010
public import Certificates.Certificate10012
public import Certificates.Certificate10013
public import Certificates.Certificate10014
public import Certificates.Certificate10016
public import Certificates.Certificate10018
public import Certificates.Certificate12041
public import Certificates.Certificate12042
public import Certificates.Certificate12043
public import Certificates.Certificate12044
public import Certificates.Certificate12045
public import Certificates.Certificate12046
public import Certificates.Certificate16015
public import Certificates.Certificate16040
public import Certificates.Certificate2154
public import Certificates.Certificate2157
public import Certificates.Certificate3006
public import Certificates.Certificate3007
public import Certificates.Certificate3008
public import Certificates.Certificate3063
public import Certificates.Certificate3077
public import Certificates.Certificate3082
public import Certificates.Certificate3083
public import Certificates.Certificate3951
public import Certificates.Certificate8026Base
public import Certificates.Certificate8171
public import Certificates.Certificate9124

public section

namespace CFSG.Open.ASVolIRegistered

open CFSG.Open
open scoped MatrixGroups

local notation "Tag" => CFSG.Assembly.LowTwoRank.StatedLieTag

theorem red_1 :
    (∀ (p f : ℕ) [Fact p.Prime] (hf : 1 ≤ f) (H : Subgroup PSL(2, GaloisField p f)),
    (IsElemAbelian p H ∧ ∃ m : ℕ, m ≤ f ∧ Nat.card H = p ^ m) ∨
    (IsCyclic H ∧ (Nat.card H ∣ (p ^ f + 1) / Nat.gcd 2 (p ^ f - 1) ∨
      Nat.card H ∣ (p ^ f - 1) / Nat.gcd 2 (p ^ f - 1))) ∨
    (∃ z : ℕ, (z ∣ (p ^ f + 1) / Nat.gcd 2 (p ^ f - 1) ∨
      z ∣ (p ^ f - 1) / Nat.gcd 2 (p ^ f - 1)) ∧ Nonempty (H ≃* DihedralGroup z)) ∨
    ((p ≠ 2 ∨ Even f) ∧ Nonempty (H ≃* alternatingGroup (Fin 4))) ∨
    (16 ∣ p ^ (2 * f) - 1 ∧ Nonempty (H ≃* Equiv.Perm (Fin 4))) ∨
    ((p = 5 ∨ 5 ∣ p ^ (2 * f) - 1) ∧ Nonempty (H ≃* alternatingGroup (Fin 5))) ∨
    (∃ (m t : ℕ) (P : Subgroup H) (_ : P.Normal), IsElemAbelian p P ∧
      Nat.card P = p ^ m ∧ IsCyclic (H ⧸ P) ∧ Nat.card (H ⧸ P) = t ∧ t ∣ p ^ m - 1 ∧
      t ∣ (p ^ f - 1) / Nat.gcd 2 (p ^ f - 1)) ∨
    (∃ m : ℕ, m ∣ f ∧ Nonempty (H ≃* PSL(2, GaloisField p m))) ∨
    (∃ m : ℕ, 2 * m ∣ f ∧ Nonempty (H ≃* PGL(2, GaloisField p m)))) := by
  intro p f _ hf H
  exact CFSG.Quasithin.F6.dicksonPSL2_holds p f hf H

local instance uniqueZModOne : Unique (ZMod 1) := inferInstanceAs (Unique (Fin 1))

local instance uniqueMultZModOne : Unique (Multiplicative (ZMod 1)) :=
  inferInstanceAs (Unique (Multiplicative (Fin 1)))

local instance uniqueZModOneProd : Unique (ZMod 1 × ZMod 1) where
  default := (default, default)
  uniq _ := Prod.ext (Unique.uniq _ _) (Unique.uniq _ _)

local instance uniqueMultZModOneProd : Unique (Multiplicative (ZMod 1) × Multiplicative (ZMod 1)) where
  default := (default, default)
  uniq _ := Prod.ext (Unique.uniq _ _) (Unique.uniq _ _)


theorem odd_pow_of_ne_two {p k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : Odd (p ^ k) :=
  (hp.odd_of_ne_two hp2).pow


section Tables

theorem griess {X : Type} [Group X] {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {n p f : ℕ}
    (h : CFSG.Blueprint.LieModel X t n p f) :
    Nonempty (griessHopfMultiplier X ≃*
      (Multiplicative (ZMod (CFSG.Blueprint.Multiplier.genericOrders t n p f).1) ×
        Multiplicative (ZMod (CFSG.Blueprint.Multiplier.genericOrders t n p f).2)) ×
      (Multiplicative (ZMod (CFSG.Blueprint.Multiplier.exceptionalOrders t n p f).1) ×
        Multiplicative (ZMod (CFSG.Blueprint.Multiplier.exceptionalOrders t n p f).2))) :=
  (CFSG.Milestones.cl_lit_griess_schur_multipliers_all_native_models X t n p f h).2


end Tables


section Final


end Final

end CFSG.Open.ASVolIRegistered
