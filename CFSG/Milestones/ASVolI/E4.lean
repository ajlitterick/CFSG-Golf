module

public import CFSG.Quasithin.Background.RonanE43M12Main
public import CFSG.Quasithin.Background.RonanE43M22Three
public import CFSG.Quasithin.Background.RonanE43M23

public section

namespace CFSG.ASVolI

namespace ChE

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E3

abbrev fStarModO2 {G : Type} [Group G] (H : Subgroup G) :
    Subgroup (↥H ⧸ CFSG.pCore 2 ↥H) :=
  CFSG.generalizedFitting (↥H ⧸ CFSG.pCore 2 ↥H)

abbrev fStarPreO2 {G : Type} [Group G] (H : Subgroup G) : Subgroup G :=
  ((fStarModO2 H).comap (QuotientGroup.mk' (CFSG.pCore 2 ↥H))).map H.subtype

end ChE

open ChE CFSG.Open CFSG.Quasithin CFSG.Quasithin.E3

@[expose] def E_4_1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ ρ : G →* MulAut V, Function.Injective ρ → pCoreOf 2 (⊤ : Subgroup G) = ⊥ →
      ∀ T : Subgroup G, IsSylowIn 2 T ⊤ → Group.IsSolvable G → Even (Nat.card G) →
        aParam ρ.range = 1


@[expose] def E_4_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ ρ : G →* MulAut V, Function.Injective ρ → pCoreOf 2 (⊤ : Subgroup G) = ⊥ →
      ∀ (T L : Subgroup G) (Δ : Set (Subgroup G)), IsSylowIn 2 T ⊤ →
        L = CFSG.generalizedFitting G → CFSG.IsQuasisimple ↥L → L ⊔ T = ⊤ →
        (⨆ H ∈ Δ, H) = ⊤ →
        (∀ H ∈ Δ, T ≤ H ∧ (CFSG.IsQuasisimple ↥(fStarModO2 H) ∨
          ∃ p : ℕ, p.Prime ∧ Nat.card ↥(fStarModO2 H) = p)) →
        (∀ H ∈ Δ, CFSG.IsQuasisimple ↥(fStarModO2 H) →
          H ≤ Subgroup.normalizer ((fStarPreO2 H ⊔ T : Subgroup G) : Set G)) →
        (∃ v ∈ fixV (T.map ρ), ∃ l ∈ L, ρ l v ≠ v) →
        aParam ρ.range ≤
          ∑ᶠ (H : Subgroup G) (_ : H ∈ Δ),
            CFSG.Open.pRank 2 (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H))


@[expose] def E_4_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ ρ : G →* MulAut V, Function.Injective ρ → pCoreOf 2 (⊤ : Subgroup G) = ⊥ →
      ∀ (T L : Subgroup G), IsSylowIn 2 T ⊤ → fixV ρ.range < fixV (T.map ρ) →
        L = CFSG.generalizedFitting G → CFSG.IsQuasisimple ↥L →
        (IsSporadic .M12 (↥L ⧸ Subgroup.center ↥L) → aParam ρ.range ≤ 2) ∧
        (IsSporadic .M22 (↥L ⧸ Subgroup.center ↥L) ∨ IsSporadic .M24 (↥L ⧸ Subgroup.center ↥L) →
          aParam ρ.range ≤ 3) ∧
        (IsSporadic .M23 G →
          (MathieuCode23 ρ.range ⊤ ⊥ ∨ MathieuCocode23 ρ.range ⊤ ⊥) → aParam ρ.range ≤ 3)

section


end

end CFSG.ASVolI
