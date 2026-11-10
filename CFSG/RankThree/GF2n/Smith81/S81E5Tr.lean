module

public import CFSG.RankThree.GF2n.Smith81.S81E5Uni
public import CFSG.RankThree.GF2n.Smith81.S81E5Gen
public import CFSG.RankThree.GF2n.Smith81.S81E7Conj
public import CFSG.RankThree.GF2n.Smith81.S81E7Form
public import CFSG.RankThree.GF2n.Smith81.Sec220TvLemmas
public import CFSG.RankThree.GF2n.Smith81.S81CS8
public import CFSG.RankThree.GF2n.Smith81.Sec220Coprime

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81.EGeom
  CFSG.LieType.Steinberg.Minuscule CFSG.RankThree.GF2n.Smith81.E7Model

@[expose] def E5RootEltStatement :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), Smith1981Below (Nat.card G) →
    RemCfg M Q Z B → InCaseE5 M Q Z B →
      ∀ (K : Type) [Field K] [Finite K] (γ : G → K) (M₀ : Tim79.QuadModel Q Z K γ),
        GlobalModelData M Q Z γ M₀ →
          ∀ (ψ : M₀.E ≃ₗ[K] V K) (φ : Lgen M (LB M Q B) →* (V K ≃ₗ[K] V K)),
            EUniData M Q Z B M₀ ψ φ (EAut K) (w0 : V K) (rootRad7 K) →
              ∀ z ∈ Z, z ≠ 1 → ∀ t : G, IsConj z t → t ∈ M → t ∉ Q →
                ∃ s : Lgen M (LB M Q B), (s : G) * t⁻¹ ∈ Q ∧ IsRootElt ((vAut K).symm (φ s))

@[expose] def Smith24E5FormStatement :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), Smith1981Below (Nat.card G) →
    RemCfg M Q Z B → InCaseE5 M Q Z B →
      ∀ (K : Type) [Field K] [Finite K] (γ : G → K) (M₀ : Tim79.QuadModel Q Z K γ),
        GlobalModelData M Q Z γ M₀ →
          ∀ (ψ : M₀.E ≃ₗ[K] V K) (φ : Lgen M (LB M Q B) →* (V K ≃ₗ[K] V K)),
            EUniData M Q Z B M₀ ψ φ (EAut K) (w0 : V K) (rootRad7 K) →
              ∃ lam : K, lam ≠ 0 ∧ ∀ e f : M₀.E, M₀.B e f = lam * beta (ψ e) (ψ f)

end CFSG.RankThree.GF2n.Smith81

namespace CFSG.RankThree.GF2n.Smith81.E5Tr

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81.EGeom
  CFSG.LieType.Steinberg.Minuscule CFSG.RankThree.GF2n.Smith81.E7Model

section Transport


end Transport

section Act


end Act

section World


end World

end CFSG.RankThree.GF2n.Smith81.E5Tr
