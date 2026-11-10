module

public import CFSG.CGT.Timmesfeld75.Config

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped MatrixGroups Matrix

@[expose] def TimmesfeldTransitivity : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (L : Subgroup X), IsWC L →
    (∀ N : Subgroup X, N.Normal → IsPGroup 2 N → N = ⊥) →
    ∀ x ∈ L, x ≠ 1 → ∀ y ∈ L, y ≠ 1 → ∃ g ∈ Subgroup.normalizer (L : Set X), g * x * g⁻¹ = y

@[expose] def Lemma214 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T : Subgroup G), IsWC T → ∀ g : G,
    conjSubgroup g T ≠ T → normIn T (conjSubgroup g T) ≠ ⊥ →
      cfgM T (conjSubgroup g T) = pCoreOf 2 (T ⊔ conjSubgroup g T) ∧
      ∃ _ : ((cfgM T (conjSubgroup g T)).subgroupOf (T ⊔ conjSubgroup g T)).Normal,
        (∃ f : ℕ, 2 ≤ f ∧ Nonempty (↥(T ⊔ conjSubgroup g T) ⧸
            (cfgM T (conjSubgroup g T)).subgroupOf (T ⊔ conjSubgroup g T) ≃*
              PSL(2, GaloisField 2 f))) ∨
        (∃ a : ℕ, 1 ≤ a ∧ Nonempty (↥(T ⊔ conjSubgroup g T) ⧸
            (cfgM T (conjSubgroup g T)).subgroupOf (T ⊔ conjSubgroup g T) ≃* Sz a)) ∨
        (∃ n : ℕ, Odd n ∧ 3 ≤ n ∧ Nonempty (↥(T ⊔ conjSubgroup g T) ⧸
            (cfgM T (conjSubgroup g T)).subgroupOf (T ⊔ conjSubgroup g T) ≃* DihedralGroup n))


end CFSG.CGT.Timmesfeld75
