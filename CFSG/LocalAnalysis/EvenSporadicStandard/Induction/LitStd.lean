module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Setting

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.Solomon78

@[expose] def IsGenQuaternion (Y : Type) [Group Y] : Prop :=
  ∃ n : ℕ, 3 ≤ n ∧ Nonempty (Y ≃* QuaternionGroup (2 ^ (n - 2)))

@[expose] def IsKleinFour (Y : Type) [Group Y] : Prop :=
  Nonempty (Y ≃* (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)))

@[expose] def EmbedsInPair {G : Type} [Group G] (K : Subgroup G) : Prop :=
  ∃ K₁ K₂ : Subgroup G, K ≤ K₁ ⊔ K₂ ∧ (K₁ ⊔ K₂).Normal ∧
    (K₁.subgroupOf (K₁ ⊔ K₂)).Normal ∧ (K₂.subgroupOf (K₁ ⊔ K₂)).Normal ∧
    Nonempty (↥K₁ ≃* ↥K) ∧ Nonempty (↥K₂ ≃* ↥K)


@[expose] def Sol78Thm46 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], CFSG.solvableRadical G = ⊥ → ∀ K : Subgroup G, SolStd K →
    ((∃ n : ℕ, 2 ≤ n ∧ LieModel (↥K ⧸ center ↥K) .PSL 3 2 n) ∨
      IsSporadic (↥K ⧸ center ↥K) .Suz ∨ IsSporadic (↥K ⧸ center ↥K) .He) →
    (IsSporadic (↥K ⧸ center ↥K) .Suz → Even (Nat.card ↥(center ↥K))) →
      EmbedsInPair K ∨
        (∃ n : ℕ, 2 ≤ n ∧ LieModel ↥K .PSL 3 2 n ∧
          LieModel ↥(Subgroup.normalClosure (K : Set G)) .PSL 3 2 (2 * n) ∧
          Nonempty (↥(centralizer (K : Set G)) ≃* Multiplicative (ZMod 2))) ∨
        (LieModel ↥K .PSL 3 2 2 ∧ IsSporadic ↥(Subgroup.normalClosure (K : Set G)) .Suz) ∨
        (IsKleinFour ↥(center ↥K) ∧ LieModel (↥K ⧸ center ↥K) .PSL 3 2 2 ∧
          IsSporadic ↥(Subgroup.normalClosure (K : Set G)) .He) ∨
        (Nonempty (↥(center ↥K) ≃* Multiplicative (ZMod 4)) ∧
          LieModel (↥K ⧸ center ↥K) .PSL 3 2 2 ∧
          IsSporadic ↥(Subgroup.normalClosure (K : Set G)) .ONan)

end CFSG.EvenSporadicStandard.Induction
