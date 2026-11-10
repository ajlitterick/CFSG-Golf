module

public import CFSG.ClassicalInvolution.RouteD.TwinSL4BridgeBase
public import CFSG.ClassicalInvolution.RouteD.TwinTenNodes
public import CFSG.ClassicalInvolution.RouteD.ExoticD4FourBasic

public section

namespace CFSG.ClassicalInvolution.Generic.CoreAssembly

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.RouteD.NonClassical
  CFSG.ClassicalInvolution.RouteD.Exotic
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)

variable {p f : ℕ} [Fact p.Prime]

@[expose] def D4LinearClique (p f : ℕ) [Fact p.Prime] (t : StatedLieTag) (n e : ℕ) : Prop :=
  ∀ (X : Type) [Group X] (φ : (modelUniv t n p e Fact.out).K →* X), φ.ker ≤ Subgroup.center _ →
    ∀ R₁ ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D,
      ∀ R₂ ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D,
        ∀ R₃ ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D, R₁ ≠ R₂ → Commutes R₁ R₂ →
          (∃ W, LinearBlockStandardPair (GaloisField p f) W (R₁.map φ) (R₃.map φ)) →
          ∃ W, LinearBlockStandardPair (GaloisField p f) W (R₂.map φ) (R₃.map φ)

@[expose] def TwinSL4Action (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z →
      LocalShapeT p f 2 .PSL 4 (conjClass K) z →
      ∀ β ∈ conjClass K, ∀ t : G, IsClassicalMember p f β t →
        (∃ W, LinearBlockStandardPair (GaloisField p f) W K β) →
        ∀ j : Fin 3 → Subgroup G, (∀ a, j a ∈ conjClass K) → (∀ a, Commutes K (j a)) →
          (∀ a : Fin 3, 1 ≤ a.val → Commutes β (j a)) → Commutes (j 1) (j 2) →
          (∃ W, LinearBlockStandardPair (GaloisField p f) W (j 0) (j 1)) →
          (∃ W, LinearBlockStandardPair (GaloisField p f) W (j 0) (j 2)) →
          ∀ x₀ : G, IsClassicalMember p f (j 1) x₀ →
            j 0 ≤ Subgroup.centralizer ({t * x₀} : Set G)


end CFSG.ClassicalInvolution.Generic.CoreAssembly
