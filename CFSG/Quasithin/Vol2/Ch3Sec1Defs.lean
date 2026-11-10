module

public import CFSG.Quasithin.Vol2.Ch3Basic
public import CFSG.Quasithin.Background.D1Statement
public import CFSG.Quasithin.Background.A4Defs
public import CFSG.LocalAnalysis.QuasithinUnique.QTKECore

public section

open CFSG.QuasithinUnique (quasithinIsQTKECat)

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

section Vocabulary

variable {G : Type} [Group G]

@[expose] noncomputable def qhatInt [Finite G] (H V : Subgroup G) (hV : IsElemAbelian 2 V) :
    WithTop ℚ :=
  @qhatOf ↥V (commGroupOfElemAbelian hV) inferInstance (autOn H V)

@[expose] def IsSQTKSub [Finite G] (H : Subgroup G) : Prop :=
  CFSG.SectionRank.IsKGroupCat ↥H ∧ CFSG.Open.SQTKTauCeti.StronglyQuasithin ↥H

structure HypC51 [Finite G] (H M₀ R TH : Subgroup G) : Prop where
  sqtk_H : IsSQTKSub H
  sqtk_M₀ : IsSQTKSub M₀
  charTwo_H : CharTwo H
  sylow_TH : IsSylowTwoOf TH H
  unique_max : ∃ N : Subgroup G, IsUniqueMaxOver H TH N
  R_le : R ≤ TH
  TH_le : TH ≤ M₀
  sylow_R : IsSylowTwoOf R (oTwoUpper H ⊔ R)
  normal_R : M₀ ≤ Subgroup.normalizer (R : Set G)

structure Hyp315Base (T M M₀ H V : Subgroup G) : Prop where
  T_le : T ≤ M₀
  le_M : M₀ ≤ M
  hStar : IsHStar T M H
  reduced : IsTwoReducedIn M₀ V
  centralizer : pCoreOf 2 M₀ = T ⊓ Subgroup.centralizer (V : Set G)

@[expose] def Hyp315.CaseI (M M₀ H : Subgroup G) : Prop :=
  H ⊓ M ≤ Subgroup.normalizer (oTwoUpper M₀ : Set G)

@[expose] def Hyp315.CaseII (M H V : Subgroup G) : Prop :=
  H ⊓ M ≤ Subgroup.normalizer (V : Set G)

structure Hyp315 (T M M₀ H V : Subgroup G) : Prop extends Hyp315Base T M M₀ H V where
  case : Hyp315.CaseI M M₀ H ∨ Hyp315.CaseII M H V

end Vocabulary

@[expose] def TheoremC58 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → quasithinIsQTKECat G → quasithinIsSylowTwo T →
    ∀ H M₀ R : Subgroup G, HypC51 H M₀ R T → R ≠ ⊥ →
      ∃ R₀ : Subgroup G, R₀ ≠ ⊥ ∧ R₀ ≤ R ∧ M₀ ⊔ H ≤ Subgroup.normalizer (R₀ : Set G)

@[expose] def Theorem311Stmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → quasithinIsQTKECat G → quasithinIsSylowTwo T →
    ∀ M₀ H R : Subgroup G, InH T M₀ → InH T H → (∃ N : Subgroup G, IsUniqueMaxOver H T N) →
      R ≠ ⊥ → R ≤ T → IsSylowTwoOf R (oTwoUpper H ⊔ R) →
      M₀ ≤ Subgroup.normalizer (R : Set G) →
      ∃ R₀ : Subgroup G, R₀ ≠ ⊥ ∧ R₀ ≤ R ∧ M₀ ⊔ H ≤ Subgroup.normalizer (R₀ : Set G)


end CFSG.Quasithin
