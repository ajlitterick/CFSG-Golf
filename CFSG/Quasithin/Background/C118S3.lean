module

public import CFSG.Quasithin.Background.C118BridgeOne

public section

namespace CFSG.Quasithin

open Subgroup CFSG CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.Campbell

abbrev ClassPred : Type 1 := ∀ {Ω : Type} [Group Ω] [Finite Ω], Subgroup Ω → Subgroup Ω → Prop

structure InClassG1 {G : Type*} [Group G] (H S : Subgroup G) : Prop where
  cls : InClassG H S
  one : IsNatL2Section (fstarPre H (VZ S H)) (Subgroup.centralizer (VZ S H : Set G))
    ⁅VZ S H, fstarPre H (VZ S H)⁆
    (⁅VZ S H, fstarPre H (VZ S H)⁆ ⊓ Subgroup.centralizer (fstarPre H (VZ S H) : Set G)) 1


@[expose] def classG1 : ClassPred := fun H S => InClassG1 H S

@[expose] def IsC118PairFor (Cls : ClassPred) {G : Type*} [Group G] (S C₁ C₂ : Subgroup G) : Prop :=
  C₁ ≠ ⊥ ∧ C₁ ≤ omegaOneCenterOf S ∧ (C₁.subgroupOf S).Characteristic ∧
    C₂ ≠ ⊥ ∧ C₂ ≤ baum S ∧ (C₂.subgroupOf (baum S)).Characteristic ∧
    ∀ (Ω : Type) [Group Ω] [Finite Ω] (H : Subgroup Ω) (ι : ↥(baum S) →* Ω),
      Function.Injective ι → Cls H ι.range →
        (C₁.subgroupOf (baum S)).map ι ≤ centerOf H ∨
        H ≤ Subgroup.normalizer (((C₂.subgroupOf (baum S)).map ι : Subgroup Ω) : Set Ω) ∨
        IsL2OrA3Block H (twoResidual H)


theorem IsC118PairFor.mono {Cls Cls' : ClassPred}
    (hCls : ∀ {Ω : Type} [Group Ω] [Finite Ω] {H B : Subgroup Ω}, Cls' H B → Cls H B)
    {G : Type*} [Group G] {S C₁ C₂ : Subgroup G} (h : IsC118PairFor Cls S C₁ C₂) :
    IsC118PairFor Cls' S C₁ C₂ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, fun Ω _ _ H ι hι hcl => h7 Ω H ι hι (hCls hcl)⟩


@[expose] def ClassSeedBridgeFor (Cls : ClassPred) : Prop :=
  ∀ (Ω : Type) [Group Ω] [Finite Ω] (B H : Subgroup Ω), baum B = B → Cls H B →
    ∃ (k : Type) (_ : Field k) (_ : Finite k) (S : Sylow 2 ↥H)
      (ρ : ↥H →* Matrix.SpecialLinearGroup (Fin 2) k)
      (ψ : Ecore ↥H →* Multiplicative (Fin 2 → k)),
      (S : Subgroup ↥H) = B.subgroupOf H ∧ IsSeed S ρ (Ecore ↥H) ψ


end CFSG.Quasithin
