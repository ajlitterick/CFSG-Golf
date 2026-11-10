module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Stages

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec5

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.Blueprint
open scoped commutatorElement

@[expose] def Prop5_1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S K₁ K₂ : Subgroup G), Std4 G z S K₁ K₂ →
    pRank 2 ↥(Qof S K₁) = 1 → pRank 2 ↥(Qof S K₂) = 1 →
    ∀ a ∈ S, orderOf a = 2 → a ∉ zpowers z → InducesFAut a K₁ → InducesFAut a K₂ →
      a ∉ commBar z

@[expose] def Lemma5_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S K₁ K₂ : Subgroup G) (a x : G),
    Ctr5 G z S K₁ K₂ a x → L52 S K₁ K₂

@[expose] def Lemma5_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S K₁ K₂ : Subgroup G) (a x : G),
    Ctr5 G z S K₁ K₂ a x → L53 z S K₁ K₂ a


@[expose] def Prop5_9 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S K₁ K₂ : Subgroup G), Std4 G z S K₁ K₂ →
    ∀ K ∈ ({K₁, K₂} : Set (Subgroup G)), 2 ≤ pRank 2 ↥(Qof S K) →
      ∀ a ∈ Qof S K, orderOf a = 2 → a ≠ z → a ∉ commBar z

@[expose] def Lemma5_10 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S K₁ K₂ : Subgroup G), Std4 G z S K₁ K₂ →
    pRank 2 ↥(Qof S K₁) = 1 → pRank 2 ↥(Qof S K₂) = 1 →
    ∀ b ∈ S, b * b ∈ Rz S z → ∀ K ∈ ({K₁, K₂} : Set (Subgroup G)), InducesFAut b K → b ∉ cSec K →
      ∃ a ∈ S, orderOf a = 2 ∧ InducesFAut a K ∧ a ∉ commBar z

end CFSG.GH74.GLS.Stage1.Thm3.Sec5
