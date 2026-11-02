module

public import CFSG.Open.TimmesfeldLargeExtraspecialMilestoneDefs
public import CFSG.Blueprint.NativeSporadic
public import CFSG.Sporadic.Co2Smith.GlC0MarkInputs
import Certificates.Kernel.Co2Smith.Cox
import Certificates.Data.Kernel.Co2Smith.Mark
import Certificates.Data.Kernel.Co2Smith.Cox
import Certificates.Kernel.Co2Smith.LettersData
import Certificates.Kernel.Co2Smith.CoxData
import Certificates.Kernel.Co2Smith.MarkK
import CFSG.LargeExtraspecial.S14Main
import CFSG.LargeExtraspecial.BridgeOrder
import CFSG.LargeExtraspecial.AS62C36Main
import CFSG.LargeExtraspecial.BridgePrinted
public import CFSG.CGT.A8S.N0EnumInputs
public import CFSG.CGT.Timmesfeld75.Derivations
public import CFSG.CGT.Timmesfeld75.Sec5One
public import CFSG.CGT.Timmesfeld75.SimpleCase
public import CFSG.CGT.Timmesfeld75.SolvableCentral
public import CFSG.CGT.Timmesfeld75.StrongClosureCentral
public import CFSG.Certificates.Kernel.Census.SiftSound
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.J3CheckInputs
public import CFSG.GH74.KGroups.L34Aut
public import CFSG.LargeExtraspecial.AS62EnumInputs
public import CFSG.LargeExtraspecial.S10SixE
public import CFSG.LargeExtraspecial.S10SixF
public import CFSG.LargeExtraspecial.S10SixH
public import CFSG.LargeExtraspecial.S10SixI
public import CFSG.LargeExtraspecial.S10SixJ
public import CFSG.LocalAnalysis.ComponentClassification.AS76bDefs
public import CFSG.LocalAnalysis.ComponentClassification.M12J2CoverExclusion
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeBridgeBase
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeCheckBase
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeModel
public import CFSG.LocalAnalysis.EvenSmallLie.Sp6JCondition
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Supercritical
public import CFSG.Quasithin.Recognition.CertTrialityCheckInputs
public import CFSG.Sporadic.Bridge.LyData
public import CFSG.Sporadic.Bridge.TableSurj
public import CFSG.Sporadic.Co2Smith.CTree
public import CFSG.Sporadic.Co2Smith.HPExclude
public import CFSG.Sporadic.Co2Smith.HPTree
public import CFSG.Sporadic.HN.LevelChainSpec
public import CFSG.Sporadic.Ly.ActionBase
public import CFSG.Sporadic.Ly.CertificateBase
public import CFSG.Sporadic.Ly.FaithSpec
public import CFSG.Sporadic.Ly.OrbitSpec
public import CFSG.Sporadic.Ly.PrimitiveBase
public import CFSG.Sporadic.LyBase
public import CFSG.Sporadic.Presentation.Ly
public import CFSG.Sporadic.Schreier.LyChain11
public import CFSG.Timmesfeld.ARS.CaseEFrame
public import CFSG.Timmesfeld.ARS.CaseMSU
public import CFSG.Timmesfeld.ARS.CaseMSpLevi
public import CFSG.Timmesfeld.ARS.Sec13Closed
public import CFSG.Timmesfeld.ARS.Sec13Maximal
public import CFSG.Timmesfeld.Bridge.RootSetsGate
public import CFSG.Timmesfeld.Bridge.RootSetsSyl
public import CFSG.Timmesfeld.Exceptional.DeepFixed
public import CFSG.Timmesfeld.Exceptional.DeepJ2Split
public import CFSG.Timmesfeld.Exceptional.DeepW1
public import CFSG.Timmesfeld.Moufang.Three
public import Certificates.Data.CFSGNative.Co2Smith.Orbit8
import CFSG.Sporadic.Th.KernelPlanes
import CFSG.Sporadic.Th.Local

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

universe u v w

namespace CFSG.Open

open CFSG.Open Matrix in
open scoped MatrixGroups in
theorem _root_.CFSG.Milestones.cl_lit_timmesfeld_1978_large_extraspecial
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (z : G) (hz : orderOf z = 2)
    (hext : timmesfeldIsExtraspecial (timmesfeldFStar (Subgroup.centralizer ({z} : Set G))))
    (w : ℕ)
    (hw : Nat.card (timmesfeldFStar (Subgroup.centralizer ({z} : Set G))) = 2 ^ (1 + 2 * w))
    (Mbar : Type) [Group Mbar]
    (hMbar : timmesfeldQuotientIso (timmesfeldFStar (Subgroup.centralizer ({z} : Set G))) Mbar) :
    w ≤ 4 ∨
    (Nonempty (G ≃* PSL(w + 2, ZMod 2)) ∨ Nonempty (G ≃* timmesfeldPSU (w + 2))) ∨
    (6 ≤ w ∧ Even w ∧
      ∃ q : QuadraticForm (ZMod 2) (Fin w → ZMod 2), timmesfeldNondegenerate q ∧
        (Nonempty (Mbar ≃* Equiv.Perm (Fin 3) × timmesfeldOmega q) ∨
          Nonempty (Mbar ≃* Equiv.Perm (Fin 3) × timmesfeldIsometries q))) ∨
    (w = 6 ∧ IsQuasisimple (timmesfeldLayer Mbar) ∧ Nat.card (timmesfeldOddCore Mbar) ≤ 3 ∧
      ∃ t : Mbar, orderOf t = 2 ∧
        ∃ R : Subgroup Mbar, R ≤ Subgroup.centralizer ({t} : Set Mbar) ∧
          (R.subgroupOf (Subgroup.centralizer ({t} : Set Mbar))).Normal ∧
          (frattini (pCoreOf 2 R)).map (pCoreOf 2 R).subtype ≤ Subgroup.zpowers t ∧
          (timmesfeldQuotientIso (pCore 2 R) PSL(3, ZMod 2) ∨
            (∃ q : QuadraticForm (ZMod 2) (Fin 4 → ZMod 2), timmesfeldNondegenerate q ∧
              timmesfeldPlusType q ∧ timmesfeldQuotientIso (pCore 2 R) (timmesfeldOmega q)) ∨
            (pCoreOf 2 R = Subgroup.zpowers t ∧
              ∃ q : QuadraticForm (ZMod 2) (Fin 6 → ZMod 2), timmesfeldNondegenerate q ∧
                timmesfeldQuotientIso (pCore 2 R) (timmesfeldOmega q)))) ∨
    (w = 10 ∧ (timmesfeldFStar Mbar).index ≤ 2 ∧
      (Nonempty (timmesfeldFStar Mbar ≃* PSL(6, ZMod 2)) ∨
        Nonempty (timmesfeldFStar Mbar ≃* timmesfeldPSU 6))) ∨
    (w = 11 ∧ IsSimpleGroup Mbar ∧ Nat.card Mbar = timmesfeldOrderCo2) ∨
    (w = 12 ∧ IsSimpleGroup Mbar ∧ Nat.card Mbar = timmesfeldOrderCo1) ∨
    (IsSimpleGroup Mbar ∧ ∃ t : Mbar, orderOf t = 2 ∧
      timmesfeldIsExtraspecial (timmesfeldFStar (Subgroup.centralizer ({t} : Set Mbar))) ∧
      ((w = 16 ∧ Nat.card (timmesfeldFStar (Subgroup.centralizer ({t} : Set Mbar))) = 2 ^ 17 ∧
          timmesfeldQuotientIso (timmesfeldFStar (Subgroup.centralizer ({t} : Set Mbar)))
            (Equiv.Perm (Fin 3) × timmesfeldOmegaPlus 4)) ∨
        (w = 28 ∧ Nat.card (timmesfeldFStar (Subgroup.centralizer ({t} : Set Mbar))) = 2 ^ 33 ∧
          timmesfeldQuotientIso (timmesfeldFStar (Subgroup.centralizer ({t} : Set Mbar)))
            (timmesfeldOmegaPlus 6)))) :=
  CFSG.LargeExtraspecial.Bridge.order_of_mainStatement
    (CFSG.LargeExtraspecial.S14.mainStatement_of_widthTwo
      CFSG.LargeExtraspecial.S14.aschbacherWidthTwoResidual_holds)
    G hnonab z hz hext w hw Mbar hMbar

end CFSG.Open

namespace CFSG.Open

open CFSG.Open Matrix in
open scoped MatrixGroups in
theorem _root_.CFSG.Milestones.cl_lit_timmesfeld_1978_large_extraspecial_models
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (z : G) (hz : orderOf z = 2)
    (hext : timmesfeldIsExtraspecial (timmesfeldFStar (Subgroup.centralizer ({z} : Set G))))
    (w : ℕ)
    (hw : Nat.card (timmesfeldFStar (Subgroup.centralizer ({z} : Set G))) = 2 ^ (1 + 2 * w))
    (Mbar : Type) [Group Mbar]
    (hMbar : timmesfeldQuotientIso (timmesfeldFStar (Subgroup.centralizer ({z} : Set G))) Mbar) :
    w ≤ 4 ∨
    (Nonempty (G ≃* PSL(w + 2, ZMod 2)) ∨ Nonempty (G ≃* timmesfeldPSU (w + 2))) ∨
    (6 ≤ w ∧ Even w ∧
      ∃ q : QuadraticForm (ZMod 2) (Fin w → ZMod 2), timmesfeldNondegenerate q ∧
        (Nonempty (Mbar ≃* Equiv.Perm (Fin 3) × timmesfeldOmega q) ∨
          Nonempty (Mbar ≃* Equiv.Perm (Fin 3) × timmesfeldIsometries q))) ∨
    (w = 6 ∧ IsQuasisimple (timmesfeldLayer Mbar) ∧ Nat.card (timmesfeldOddCore Mbar) ≤ 3 ∧
      ∃ t : Mbar, orderOf t = 2 ∧
        ∃ R : Subgroup Mbar, R ≤ Subgroup.centralizer ({t} : Set Mbar) ∧
          (R.subgroupOf (Subgroup.centralizer ({t} : Set Mbar))).Normal ∧
          (frattini (pCoreOf 2 R)).map (pCoreOf 2 R).subtype ≤ Subgroup.zpowers t ∧
          (timmesfeldQuotientIso (pCore 2 R) PSL(3, ZMod 2) ∨
            (∃ q : QuadraticForm (ZMod 2) (Fin 4 → ZMod 2), timmesfeldNondegenerate q ∧
              timmesfeldPlusType q ∧ timmesfeldQuotientIso (pCore 2 R) (timmesfeldOmega q)) ∨
            (pCoreOf 2 R = Subgroup.zpowers t ∧
              ∃ q : QuadraticForm (ZMod 2) (Fin 6 → ZMod 2), timmesfeldNondegenerate q ∧
                timmesfeldQuotientIso (pCore 2 R) (timmesfeldOmega q)))) ∨
    (w = 10 ∧ (timmesfeldFStar Mbar).index ≤ 2 ∧
      (Nonempty (timmesfeldFStar Mbar ≃* PSL(6, ZMod 2)) ∨
        Nonempty (timmesfeldFStar Mbar ≃* timmesfeldPSU 6)) ∧
      ∃ σ : Mbar, σ * σ = 1 ∧
        timmesfeldFStar Mbar ⊔ Subgroup.zpowers σ = ⊤) ∨
    (w = 11 ∧ Nonempty (Mbar ≃* Blueprint.NativeSporadic.Co2)) ∨
    (w = 12 ∧ Nonempty (Mbar ≃* Blueprint.NativeSporadic.Co1)) ∨
    (IsSimpleGroup Mbar ∧ ∃ t : Mbar, orderOf t = 2 ∧
      timmesfeldIsExtraspecial (timmesfeldFStar (Subgroup.centralizer ({t} : Set Mbar))) ∧
      ((w = 16 ∧ Nat.card (timmesfeldFStar (Subgroup.centralizer ({t} : Set Mbar))) = 2 ^ 17 ∧
          timmesfeldQuotientIso (timmesfeldFStar (Subgroup.centralizer ({t} : Set Mbar)))
            (Equiv.Perm (Fin 3) × timmesfeldOmegaPlus 4)) ∨
        (w = 28 ∧ Nat.card (timmesfeldFStar (Subgroup.centralizer ({t} : Set Mbar))) = 2 ^ 33 ∧
          timmesfeldQuotientIso (timmesfeldFStar (Subgroup.centralizer ({t} : Set Mbar)))
            (timmesfeldOmegaPlus 6)))) :=
  CFSG.LargeExtraspecial.Bridge.printed_of_mainStatement
    (CFSG.LargeExtraspecial.S14.mainStatement_of_widthTwo
      CFSG.LargeExtraspecial.S14.aschbacherWidthTwoResidual_holds)
    G hnonab z hz hext w hw Mbar hMbar

end CFSG.Open
