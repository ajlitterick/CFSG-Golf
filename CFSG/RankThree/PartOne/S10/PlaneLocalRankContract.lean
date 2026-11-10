module

public import CFSG.RankThree.PartOne.S10.CentralCoverContract
public import CFSG.LocalAnalysis.ComponentClassification.PerfectAutomorphisms
public import CFSG.LocalAnalysis.ComponentInitial.CoprimeCommutatorFactorization

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree.CentralCover
open CFSG.LocalAnalysis.ComponentInitial

@[expose] noncomputable def centerQuotientConjOfLe {H : Type} [Group H] (X M : Subgroup H)
    (hM : M ≤ Subgroup.normalizer (X : Set H)) : M →* MulAut (↥X ⧸ Subgroup.center ↥X) :=
  (ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥X).comp
    (X.normalizerMonoidHom.comp (Subgroup.inclusion hM))


structure SourceSixThirteenSetup {H : Type} [Group H] (X A₀ : Subgroup H) (b c y : H) : Prop where
  quasisimple : CFSG.IsQuasisimple ↥X
  normalizes : A₀ ≤ Subgroup.normalizer (X : Set H)
  elementary : IsElementaryAbelian 5 A₀
  card : Nat.card A₀ = 125
  generated : A₀ = Subgroup.zpowers b ⊔ Subgroup.zpowers c ⊔ Subgroup.zpowers y
  centralizer_eq : A₀ ⊓ Subgroup.centralizer (X : Set H) = Subgroup.zpowers b
  y_mem : y ∈ X


theorem SourceSixThirteenSetup.c_mem {H : Type} [Group H] {X A₀ : Subgroup H} {b c y : H}
    (h : SourceSixThirteenSetup X A₀ b c y) : c ∈ A₀ := by
  rw [h.generated]
  exact Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers c))


namespace SourceSixThirteen

variable {H : Type} [Group H] {X A₀ : Subgroup H} {b c y : H}

@[expose] noncomputable def lam (h : SourceSixThirteenSetup X A₀ b c y) :
    A₀ →* MulAut (↥X ⧸ Subgroup.center ↥X) :=
  centerQuotientConjOfLe X A₀ h.normalizes

@[expose] noncomputable def beta (h : SourceSixThirteenSetup X A₀ b c y) :
    MulAut (↥X ⧸ Subgroup.center ↥X) :=
  lam h ⟨c, h.c_mem⟩


end SourceSixThirteen

end CFSG.RankThree.PartOne
