module

public import CFSG.LocalAnalysis.StandardType.GGSixAutKFlatIVPComp
public import CFSG.LocalAnalysis.AGLEmbedding.PushingUpLemmas
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreQuotient
public import CFSG.RankThree.GroupTheory.PerfectSubnormalModNormal
public import CFSG.Permutation.FiveTransitive.CharacteristicAutomorphism
public import CFSG.Fischer.Aut.TwoPower
public import CFSG.GroupTheory.CenterlessInnerCentralizer
public import CFSG.GroupTheory.CommutingConjugatePair
public import CFSG.Assembly.QuasithinDefs
public import CFSG.GroupTheory.PCore.SubgroupCore
public import CFSG.HardMathSupport.Solomon.LocalBalance.Defs
public import CFSG.LocalAnalysis.AGLEmbedding.Reduction
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingTransport
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.ComponentInitial.PerfectOuterInjection
public import CFSG.LocalAnalysis.GLTheoremB.UniqInputs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

open scoped commutatorElement

section Quotient

variable {H : Type*} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]


end Quotient

section Ambient

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]


end Ambient


section RootAction

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
variable {X A : Subgroup G}

@[expose] def ggPComponentRootKernelInA (p : ℕ) (A : Subgroup G) : Subgroup ↥A :=
  (Subgroup.center (↥A ⧸ CFSG.pPrimeCore p A)).comap
    (QuotientGroup.mk' (CFSG.pPrimeCore p A))


instance ggPComponentRootKernelInA_normal (p : ℕ) (A : Subgroup G) :
    (ggPComponentRootKernelInA p A).Normal :=
  (inferInstance : (Subgroup.center (↥A ⧸ CFSG.pPrimeCore p A)).Normal).comap
    (QuotientGroup.mk' (CFSG.pPrimeCore p A))


instance ggPComponentRootKernelInA_characteristic (p : ℕ) (A : Subgroup G) :
    (ggPComponentRootKernelInA p A).Characteristic :=
  Subgroup.Characteristic.comap_quotient_mk (H := CFSG.pPrimeCore p A)
    (K := Subgroup.center (↥A ⧸ CFSG.pPrimeCore p A))
    (inferInstance : (Subgroup.center (↥A ⧸ CFSG.pPrimeCore p A)).Characteristic)


end RootAction

section RootActionTransport


end RootActionTransport

end CFSG.StandardType
