module

public import CFSG.RankThree.GF2n.Smith81.S81D6W
public import CFSG.RankThree.GF2n.Smith81.S81BGeom
public import CFSG.RankThree.GF2n.Smith81.S81CCases

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.D6Spin

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81
  CFSG.RankThree.GF2n.Smith81.EGeom CFSG.LieType.Steinberg.Minuscule
  CFSG.RankThree.GF2n.Smith81.E7Model

section ToUniform

variable
  {G : Type} [Group G] {K : Type} [Field K] [Finite K]
  {M Q Z B : Subgroup G} {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
  [(Z.subgroupOf Q).Normal]
  {φ₀ : Lgen M (LB M Q B) →* (Module.End K (W K))ˣ}
  {ψ₀ : ↥Q ⧸ Z.subgroupOf Q ≃* Multiplicative (W K)}


end ToUniform

@[expose] def Smith24E4UniformStatement :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), Smith1981Below (Nat.card G) →
    RemCfg M Q Z B → InCaseE4 M Q Z B →
      ∀ (K : Type) [Field K] [Finite K] (γ : G → K) (M₀ : Tim79.QuadModel Q Z K γ),
        GlobalModelData M Q Z γ M₀ →
          ∃ (ψ : M₀.E ≃ₗ[K] W K) (φ : Lgen M (LB M Q B) →* (W K ≃ₗ[K] W K)),
            EUniData M Q Z B M₀ ψ φ (EAut0 K) (p0 K) (rootRad0 K)

@[expose] def E4RootEltStatement :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), Smith1981Below (Nat.card G) →
    RemCfg M Q Z B → InCaseE4 M Q Z B →
      ∀ (K : Type) [Field K] [Finite K] (γ : G → K) (M₀ : Tim79.QuadModel Q Z K γ),
        GlobalModelData M Q Z γ M₀ →
          ∀ (ψ : M₀.E ≃ₗ[K] W K) (φ : Lgen M (LB M Q B) →* (W K ≃ₗ[K] W K)),
            EUniData M Q Z B M₀ ψ φ (EAut0 K) (p0 K) (rootRad0 K) →
              ∀ z ∈ Z, z ≠ 1 → ∀ t : G, IsConj z t → t ∈ M → t ∉ Q →
                ∃ s : Lgen M (LB M Q B), (s : G) * t⁻¹ ∈ Q ∧ IsRootEltW ((vAut0 K).symm (φ s))

@[expose] def Smith24E4FormStatement :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), Smith1981Below (Nat.card G) →
    RemCfg M Q Z B → InCaseE4 M Q Z B →
      ∀ (K : Type) [Field K] [Finite K] (γ : G → K) (M₀ : Tim79.QuadModel Q Z K γ),
        GlobalModelData M Q Z γ M₀ →
          ∀ (ψ : M₀.E ≃ₗ[K] W K) (φ : Lgen M (LB M Q B) →* (W K ≃ₗ[K] W K)),
            EUniData M Q Z B M₀ ψ φ (EAut0 K) (p0 K) (rootRad0 K) →
              ∃ lam : K, lam ≠ 0 ∧ ∀ e f : M₀.E, M₀.B e f = lam * betaW (ψ e) (ψ f)

end CFSG.RankThree.GF2n.Smith81.D6Spin
