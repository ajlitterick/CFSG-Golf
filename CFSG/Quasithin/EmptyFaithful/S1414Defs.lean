module

public import CFSG.Quasithin.EmptyFaithful.S141
public import CFSG.Quasithin.EmptyFaithful.S1417System
public import CFSG.Quasithin.Background.B6Defs
public import CFSG.Quasithin.Background.A4Defs
public import CFSG.Quasithin.Background.B2FactorizationBridge
public import CFSG.Quasithin.Background.A3ComponentsBasic
public import CFSG.Quasithin.EmptyFaithful.Vocabulary

public section

open CFSG.QuasithinUnique (quasithinIsQTKECat)

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

@[expose] def StageLemma1414 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → quasithinIsQTKECat G → quasithinIsSylowTwo T →
    (∀ L : Subgroup G, ¬ quasithinIsFaithfulLocal T L) →
    ∀ M : Subgroup G, IsOrdMaximal T M → thompsonJ T ≤ M ⊓ Subgroup.centralizer (VZ T M : Set G) →
      IsGreatestOrd T M

@[expose] def Theorem311 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → quasithinIsQTKECat G → quasithinIsSylowTwo T →
    ∀ M₀ H R : Subgroup G, InH T M₀ → InH T H → (∃ N : Subgroup G, IsUniqueMaxOver H T N) →
      R ≠ ⊥ → R ≤ T → IsSylowTwoOf R (oTwoUpper H ⊔ R) →
      M₀ ≤ Subgroup.normalizer (R : Set G) →
      ∃ R₀ : Subgroup G, R₀ ≠ ⊥ ∧ R₀ ≤ R ∧ M₀ ⊔ H ≤ Subgroup.normalizer (R₀ : Set G)


end CFSG.Quasithin
