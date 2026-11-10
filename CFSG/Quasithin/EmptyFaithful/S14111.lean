module

public import CFSG.Quasithin.EmptyFaithful.S14112
public import CFSG.Quasithin.EmptyFaithful.S141Statements
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.Blocks
public import CFSG.LinearAlgebra.LinearGroups.Perfect

public section

open CFSG.QuasithinUnique (quasithinIsQTKECat)

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

variable {G : Type*} [Group G]

@[expose] def IsChiBlock (X L : Subgroup G) : Prop :=
  IsBlock2 X L ∧ ((∃ n : ℕ, 1 < n ∧ IsLin2Type L n) ∨ ∃ m : ℕ, Odd m ∧ 3 ≤ m ∧ IsAltType L m)


@[expose] def StageLemma14110 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc : Subgroup G), quasithinQTFE14Cat G T Mc →
    ∀ M X R : Subgroup G, InM T M → IsBlock2 M X → IsAltType X 3 → pCoreOf 2 M ≤ R → R ≤ T →
      ⁅X, thompsonJ R⁆ = X → M = Mc ∧ 2 < Nat.card (quasithinOmegaOneCenter T)

@[expose] def StageLemma1417Stab : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc : Subgroup G), quasithinQTFE14Cat G T Mc →
    ∀ M V : Subgroup G, InM T M → IsTwoReducedIn M V →
      ¬ thompsonJ T ≤ M ⊓ Subgroup.centralizer (V : Set G) →
      (M ≠ Mc ∨ Nat.card (quasithinOmegaOneCenter T) = 2) →
      M ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ≤
        (M ⊓ Subgroup.centralizer (V : Set G)) ⊔ T

section Reduction


end Reduction

end CFSG.Quasithin
