module

public import CFSG.Quasithin.Background.HL3WrBlock
public import CFSG.Quasithin.Background.RonanH43One
public import CFSG.Quasithin.Background.RonanH43Two
public import CFSG.Quasithin.Background.RonanH49Orbit
public import CFSG.Quasithin.Background.RonanH49Wr
public import CFSG.Quasithin.Background.RonanH49Chief
public import CFSG.Quasithin.Background.RonanH49Y
public import CFSG.Quasithin.Background.RonanH49D
public import CFSG.Quasithin.Background.RonanH49Tr
public import CFSG.Quasithin.Background.RonanH49Irr
public import CFSG.Quasithin.Background.RonanH412Main
public import CFSG.Quasithin.Background.RonanH44Six
public import CFSG.Quasithin.Background.RonanH44TwoMain
public import CFSG.Quasithin.Background.RonanH44Num
public import CFSG.Quasithin.Background.RonanH44Five
public import CFSG.Quasithin.Background.RonanH45D
public import CFSG.Quasithin.Background.RonanH46One
public import CFSG.Quasithin.Background.RonanH46Three
public import CFSG.Quasithin.Background.RonanH46TwoB
public import CFSG.Quasithin.Background.RonanH46Chief
public import CFSG.Quasithin.Background.RonanH46ChiefTop
public import CFSG.Quasithin.Background.RonanH46Transv
public import CFSG.Quasithin.Background.RonanH46TransvFull
public import CFSG.Quasithin.Background.RonanH46OzZ
public import CFSG.Quasithin.Background.H47WMain
public import CFSG.Sporadic.Schreier.J4SCommGenBase1
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.GH74.GLS.IVK.L2.Hilbert90Core
public import CFSG.GH74.SmallRanks.AltM11
public import CFSG.LieType.SteinbergBRTwoRankBound
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
public import CFSG.LocalAnalysis.ComponentInitial.CommutingBlock
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldNaturalAction
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57Sp4
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftSaturate
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalFamily
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalLinearStrong
public import CFSG.Quasithin.Background.FFC4Pair
public import CFSG.Quasithin.Background.FFC4Tr2
public import CFSG.Quasithin.Background.HFF
public import CFSG.Quasithin.Background.HPairBridge
public import CFSG.Quasithin.Background.HSL3Inner
public import CFSG.Quasithin.Background.RonanH412Odd
public import CFSG.Quasithin.Background.SmithB42L2L32
public import CFSG.Quasithin.Background.SmithB42L2Nat
public import CFSG.Quasithin.Background.SmithB42SL3Key
public import CFSG.Quasithin.Background.SmithB45SL3Label
public import CFSG.Quasithin.Background.SmithB45SL3Outer
public import CFSG.Quasithin.Background.SmithB51LnRealB
public import Certificates.Data.CFSGNative.MonsterB.Rep4371Model
public import Certificates.Kernel.J4Count.FixCE
public import Certificates.Kernel.J4Count.FixCPairBase1

public section

open scoped commutatorElement MatrixGroups

namespace CFSG.ASVolI.ChH

open CFSG.Quasithin CFSG.Open

section Pair

open CFSG.Quasithin.H.SL3Pair


end Pair

section Nine

open CFSG.Quasithin.H.L3Nine CFSG.Quasithin.H.SU3 Matrix

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}


end Nine

section Wr

open CFSG.Quasithin.H.L3Wr


end Wr

end CFSG.ASVolI.ChH

namespace CFSG.ASVolI

open CFSG.Quasithin CFSG.ASVolI.ChH CFSG.Quasithin.H.SL3Pair CFSG.Quasithin.H.L3Wr


section H42


end H42


section H44glue

open CFSG.Quasithin.H.L3Nine CFSG.Quasithin.H.SU3 Matrix

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}


end H44glue


open CFSG.Quasithin.H.L3Nine CFSG.Quasithin.H.SU3 in
@[expose] def H_4_7 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
  ∀ (M : Subgroup (MulAut V)) (K : Type) [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = (2 ^ 1) ^ 2),
    Nonempty (↥(CFSG.generalizedFitting ↥M) ≃* PSL(3, K)) →
    IsIrredOn ((CFSG.generalizedFitting ↥M).map M.subtype) ⊤ →
    ∀ t ∈ M, orderOf t = 2 →
      3 ≤ rk ↥(commV (Subgroup.zpowers t)) ∧
      (rk ↥(commV (Subgroup.zpowers t)) = 3 ↔
        ∃ e : V ≃* HMod 1 K,
          ((CFSG.generalizedFitting ↥M).map M.subtype).map (MulAut.congr e).toMonoidHom = img hK ∧
          ∃ l ∈ img hK, ∃ φ : K ≃+* K, φ ≠ 1 ∧ MulAut.congr e t = l * fldAut φ)

section H47

theorem as_H_4_7 : H_4_7 := by
  unfold H_4_7
  intro V _ _ hV M K _ _ _ hK hL hirr t htM ht2
  exact CFSG.Quasithin.H47W.H47_main V hV M K hK hL hirr t htM ht2

end H47


section WrH48


end WrH48


section WrH410

open CFSG.Quasithin.H.L3Wr
open scoped Matrix


end WrH410


end CFSG.ASVolI
