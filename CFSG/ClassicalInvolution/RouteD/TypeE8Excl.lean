module

public import CFSG.ClassicalInvolution.RouteD.TypeE8Model
public import CFSG.ClassicalInvolution.RouteD.TypeTwistedE6PerpShape
public import CFSG.ClassicalInvolution.Balance.PassTwoFinal
public import CFSG.ClassicalInvolution.RouteD.GapsChainConfig
public import CFSG.ClassicalInvolution.RouteD.LocalTwinBAdapt
public import CFSG.ClassicalInvolution.RouteD.LocalTwinBWeakNodes
public import CFSG.ClassicalInvolution.RouteD.TypeEAdapt
public import CFSG.ClassicalInvolution.RouteD.TypeEPatternTorGeom
public import CFSG.ClassicalInvolution.RouteD.TypeEPatternToral
public import CFSG.ClassicalInvolution.RouteD.TypeTwistedE6PerpBasic
public import CFSG.ClassicalInvolution.RouteD.TypeTwistedE6TwinMain

public section

namespace CFSG.ClassicalInvolution.RouteD.TypeE8

open CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Generic.CoreAssembly
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.ClassicalInvolution.RouteD.NonClassical (PerpTableR)
open CFSG.LieType.Steinberg.Adjoint (iform)
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)

local notation "𝒞" => Generic.CoreAssembly.conjClass

@[expose] def D8NoThreeAdjPairs (p : ℕ) [Fact p.Prime] (t : StatedLieTag) (n e : ℕ) : Prop :=
  ∀ P : Fin 3 → Fin 2 → Subgroup (modelUniv t n p e Fact.out).K,
    (∀ i j, P i j ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D) →
    (∀ i, Gaps.ModelAdj (Subgroup.center (modelUniv t n p e Fact.out).K) (P i 0) (P i 1) ∧
      ∃ W, LinearBlockStandardPair (GaloisField p e) W (P i 0) (P i 1)) →
    (∀ i i', i ≠ i' → ∀ j j', Commutes (P i j) (P i' j')) → False

variable (p f : ℕ) [Fact p.Prime]

noncomputable abbrev Rroot (δ : Fin 7 → ℤ) : Subgroup (K7 p f) :=
  (D7 p f).rootGroup δ ⊔ (D7 p f).rootGroup (-δ)

section Toral

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}

@[expose] def ToralNormalAt (c : ETCtx p f .E7 0 Ω K z) {t : G} (ht : t * z * t⁻¹ = z)
    (g : K7 p f) (p₀ : Fin 7) : Prop :=
  ∀ γ ∈ (D7 p f).roots,
    ((conjSub g (Rroot p f γ)).map c.d.ψ).map (Gaps.locAut c.hΩ.conjInvariant ht).toMonoidHom =
      (conjSub g (Rroot p f γ)).map c.d.ψ ∧
    ((∀ x ∈ (conjSub g (Rroot p f γ)).map c.d.ψ, Gaps.locAut c.hΩ.conjInvariant ht x = x) ↔
      ((γ p₀ : ℤ) : ZMod 2) = 0)

end Toral

@[expose] def E8ClassExcluded : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z → LocalShapeT p f 1 .E7 0 (𝒞 K) z →
      ∀ c : ETCtx p f .E7 0 (𝒞 K) K z, ∀ β ∈ 𝒞 K, ∀ t : G, IsClassicalMember p f β t →
        (∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W K β) →
        ∀ ht : t * z * t⁻¹ = z, ∀ (g : K7 p f) (p₀ : Fin 7),
          ToralNormalAt p f c ht g p₀ → p₀ = 6

@[expose] def E7FrameRelations : Prop :=
  ∀ (g : K7 p f) (δ δ' : Fin 7 → ℤ), δ ∈ (D7 p f).roots → δ' ∈ (D7 p f).roots →
    conjSub g (Rroot p f δ) ∈ F7 p f ∧
    (iform (τ := .E7) δ δ' = 0 →
      Commutes (conjSub g (Rroot p f δ)) (conjSub g (Rroot p f δ'))) ∧
    (iform (τ := .E7) δ δ' = -1 →
      Gaps.ModelAdj (Subgroup.center (K7 p f)) (conjSub g (Rroot p f δ))
          (conjSub g (Rroot p f δ')) ∧
        ∃ W, LinearBlockStandardPair (GaloisField p f) W (conjSub g (Rroot p f δ))
          (conjSub g (Rroot p f δ')))

@[expose] def E7FrameInvolutions : Prop :=
  ∀ (g : K7 p f) (δ₁ δ₂ : Fin 7 → ℤ), δ₁ ∈ (D7 p f).roots → δ₂ ∈ (D7 p f).roots →
    iform (τ := .E7) δ₁ δ₂ = 0 →
    ∀ r₁ ∈ conjSub g (Rroot p f δ₁), ∀ r₂ ∈ conjSub g (Rroot p f δ₂), orderOf r₁ = 2 →
      orderOf r₂ = 2 →
      r₁ ∉ Subgroup.center (K7 p f) ∧ r₂ ∉ Subgroup.center (K7 p f) ∧
      r₁ * r₂ ∉ Subgroup.center (K7 p f) ∧
      ∀ δ ∈ (D7 p f).roots, (iform (τ := .E7) δ δ₁ + iform (τ := .E7) δ δ₂) % 2 = 0 →
        conjSub g (Rroot p f δ) ≤ Subgroup.centralizer ({r₁ * r₂} : Set (K7 p f))

@[expose] def E7PerpA2StarFree : Prop :=
  ∀ A ∈ F7 p f, ∀ B ∈ F7 p f, Gaps.ModelAdj (Subgroup.center (K7 p f)) A B →
    (∃ W, LinearBlockStandardPair (GaloisField p f) W A B) →
    ∀ C ∈ F7 p f, ∀ L₁ ∈ F7 p f, ∀ L₂ ∈ F7 p f, ∀ L₃ ∈ F7 p f,
      Commutes C A → Commutes C B → Commutes L₁ A → Commutes L₁ B → Commutes L₂ A →
      Commutes L₂ B → Commutes L₃ A → Commutes L₃ B →
      (∃ W, LinearBlockStandardPair (GaloisField p f) W C L₁) →
      (∃ W, LinearBlockStandardPair (GaloisField p f) W C L₂) →
      (∃ W, LinearBlockStandardPair (GaloisField p f) W C L₃) →
      Commutes L₁ L₂ → Commutes L₁ L₃ → Commutes L₂ L₃ → False


@[expose] def E8P1x : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z → ∀ (W₁ W₂ : Subgroup G) (w₁ w₂ : G),
      W₁ ∈ 𝒞 K → W₂ ∈ 𝒞 K → IsClassicalMember p f W₁ w₁ → IsClassicalMember p f W₂ w₂ →
      Commutes K W₁ → Commutes K W₂ → Commutes W₁ W₂ →
      Nat.card (Subgroup.closure ({z, w₁, w₂} : Set G)) = 8 → LocalOddCentral (𝒞 K) {w₁ * w₂}

@[expose] def E8R1Excluded : Prop :=
  Gaps.FundNoncentral p → E7FrameRelations p f → E7PerpA2StarFree p f →
    ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
      ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z → LocalShapeT p f 1 .E7 0 (𝒞 K) z →
        ∀ c : ETCtx p f .E7 0 (𝒞 K) K z, ∀ β ∈ 𝒞 K, ∀ t : G, IsClassicalMember p f β t →
          (∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W K β) →
          ∀ ht : t * z * t⁻¹ = z, ∀ (g : K7 p f) (p₀ : Fin 7),
            (p₀ = 0 ∨ p₀ = 2 ∨ p₀ = 3 ∨ p₀ = 5) → ToralNormalAt p f c ht g p₀ → False


end CFSG.ClassicalInvolution.RouteD.TypeE8
