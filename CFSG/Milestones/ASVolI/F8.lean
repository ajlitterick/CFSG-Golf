module

public import CFSG.Milestones.ASVolI.F7

public section

namespace CFSG.ASVolI.ChF

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.CosetGeom CFSG.Quasithin.F7

abbrev HypF_8_1 {G : Type} [Group G] (T V L V₁ H : Subgroup G) : Prop := HypF81 T V L V₁ H

end CFSG.ASVolI.ChF

namespace CFSG.ASVolI

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.CosetGeom CFSG.Quasithin.F7
open CFSG.ASVolI.ChF
open scoped Pointwise

@[expose] def F_8_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T V L V₁ H : Subgroup G), HypF_8_1 T V L V₁ H →
    AlmostSpecialHyp V V₁ L T H ∧
    ((conjClosure V H ≤ pCoreOf 2 H ∧
        (∀ u ∈ conjClosure V H, ∀ q ∈ pCoreOf 2 H, u * q * u⁻¹ * q⁻¹ ∈ V₁) ∧
        ∀ u ∈ conjClosure V H, u ^ 2 ∈ V₁) ∧
      (∀ D : Subgroup G, D ≤ H → H ≤ Subgroup.normalizer (D : Set G) →
        (∀ d ∈ D, ∃ k : ℕ, d ^ 2 ^ k ∈ centralizerMod V₁ H (conjClosure V H)) →
          D ≤ centralizerMod V₁ H (conjClosure V H)) ∧
      IsPGroup 2 (conjClosure V H)) ∧
    frattiniOf (conjClosure V H) ≤ V₁ ∧
    pCoreOf 2 H = centralizerMod V₁ H (conjClosure V H)


@[expose] def F_8_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T V L V₁ H : Subgroup G), HypF_8_1 T V L V₁ H →
    HypF_7_6 ((L ⊔ T) ⊔ H) (L ⊔ T) H T V ∧ (L ⊔ T) ⊓ H = L₁Of L V₁ ⊔ T


@[expose] def F_8_4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T V L V₁ H : Subgroup G), HypF_8_1 T V L V₁ H →
    conjClosure V H = Vv V (F8.γ₁ T L H) ∧
    (∃ γ : F8.Geom T L H, IsCriticalVertex ((L ⊔ T) ⊔ H) (L ⊔ T) H V γ) ∧
    ∃ (γ γ' : F8.Geom T L H) (g : ↥((L ⊔ T) ⊔ H)), F8Setup T V L H γ γ' g


@[expose] def F_8_5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T V L V₁ H : Subgroup G), HypF_8_1 T V L V₁ H →
    (3 ≤ F8.b T V L H ∧ Odd (F8.b T V L H)) ∧
    IsElemAbelian 2 (conjClosure V H)


@[expose] def F_8_6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T V L V₁ H : Subgroup G) (γ γ' : F8.Geom T L H)
    (g : ↥((L ⊔ T) ⊔ H)), HypF_8_1 T V L V₁ H → F8Setup T V L H γ γ' g →
      conjSub (g : G) (L₁Of L V₁) = oTwoRes (stab γ' ⊓ stab γ)


@[expose] def F_8_7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T V L V₁ H : Subgroup G) (γ γ' : F8.Geom T L H)
    (g : ↥((L ⊔ T) ⊔ H)), HypF_8_1 T V L V₁ H → F8Setup T V L H γ γ' g →
      stab (F8.γ₀ T L H) ⊓ stab (F8.γ₁ T L H) = L₁Of L V₁ ⊔ T ∧
      (conjClosure V H ≤ pCoreOf 2 (stab γ' ⊓ stab γ) ∧
        ∀ γ₂ ∈ nbrs (F8.γ₁ T L H), CosetGeom.dist γ γ₂ + 2 = F8.b T V L H →
          F8.Uγ V H (g : G) ≤ pCoreOf 2 (stab (F8.γ₁ T L H) ⊓ stab γ₂)) ∧
      ⁅conjClosure V H, F8.Uγ V H (g : G)⁆ ≤ conjClosure V H ⊓ F8.Uγ V H (g : G) ∧
      F8.Uγ V H (g : G) ≤ Subgroup.normalizer (Vv V (F8.γ₁ T L H) : Set G) ∧
      (¬ ⁅F8.Uγ V H (g : G), V⁆ ≤ F8.A₁ V₁ (g : G) ∧ V₁ ⊓ F8.A₁ V₁ (g : G) = ⊥) ∧
      (⁅F8.Uγ V H (g : G), F8.DH V V₁ H (g : G)⁆ ≤ F8.A₁ V₁ (g : G) ∧
        ⁅conjClosure V H, F8.Dγ V V₁ H (g : G)⁆ ≤ V₁) ∧
      ⁅F8.DH V V₁ H (g : G), F8.Dγ V V₁ H (g : G)⁆ = ⊥


end CFSG.ASVolI
