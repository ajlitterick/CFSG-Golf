module

public import CFSG.GH74.GLS.Types

public section

namespace CFSG.GH74.GLS

open Subgroup Blueprint Assembly.LowTwoRank
open scoped commutatorElement

@[expose] def SameInvolutionFusionPattern (G : Type*) [Group G] (G' : Type*) [Group G'] : Prop :=
  ∃ (S : Sylow 2 G) (S' : Sylow 2 G') (φ : ↥(S : Subgroup G) ≃* ↥(S' : Subgroup G')),
    ∀ u v : ↥(S : Subgroup G), orderOf u = 2 → orderOf v = 2 →
      (IsConj (u : G) (v : G) ↔ IsConj (φ u : G') (φ v : G'))

@[expose] def SameCentralizerOfInvolutionPattern (G : Type*) [Group G] (G' : Type*) [Group G'] :
    Prop :=
  ∃ (S : Sylow 2 G) (S' : Sylow 2 G') (φ : ↥(S : Subgroup G) ≃* ↥(S' : Subgroup G')),
    (∀ u v : ↥(S : Subgroup G), orderOf u = 2 → orderOf v = 2 →
      (IsConj (u : G) (v : G) ↔ IsConj (φ u : G') (φ v : G'))) ∧
    ∀ u : ↥(S : Subgroup G), orderOf u = 2 →
      Nonempty (↥(centralizer ({(u : G)} : Set G)) ≃* ↥(centralizer ({(φ u : G')} : Set G')))

@[expose] def IsApproxTo (G : Type) [Group G] (Gs : Type) [Group Gs] : Prop :=
  SameCentralizerOfInvolutionPattern G Gs ∧
    ((Nonempty (Gs ≃* alternatingGroup (Fin 7)) ∨ NativeSporadic.IsSporadic Gs .M11) →
      Nat.card G = Nat.card Gs)

section Helpers

variable {X : Type*} [Group X]

@[expose] def IsInternalDirectProduct (A B H : Subgroup X) : Prop :=
  A ⊔ B = H ∧ (∀ a ∈ A, ∀ b ∈ B, a * b = b * a) ∧ A ⊓ B = ⊥

@[expose] def IsCentralProductOfSL2 (K : Subgroup X) (F₁ F₂ : Type) [Field F₁] [Field F₂] : Prop :=
  ∃ A B : Subgroup X, A ⊔ B = K ∧ (∀ a ∈ A, ∀ b ∈ B, a * b = b * a) ∧ Nat.card ↥(A ⊓ B) = 2 ∧
    Nonempty (↥A ≃* StatedSL 2 F₁) ∧ Nonempty (↥B ≃* StatedSL 2 F₂)

@[expose] def zElt (z : X) : ↥(centralizer ({z} : Set X)) :=
  ⟨z, mem_centralizer_singleton_iff.mpr rfl⟩

@[expose] def zBar (z : X) : CentralizerBar z := QuotientGroup.mk (zElt z)

@[expose] def IsNonabelianMaximalClassTwoGroup (P : Type*) [Group P] : Prop :=
  IsPGroup 2 P ∧ ¬ IsMulCommutative P ∧ ∃ _ : Group.IsNilpotent P,
    Nat.card P = 2 ^ (Group.nilpotencyClass P + 1)

@[expose] def HasSL2ProductOfIndexTwoStage1 (C₁ : Subgroup X) (q : ℕ) : Prop :=
  ∃ (F₁ F₂ : Type) (_ : Field F₁) (_ : Field F₂) (_ : Finite F₁) (_ : Finite F₂),
    Odd (Nat.card F₁) ∧ Odd (Nat.card F₂) ∧ Nat.card F₂ ≤ Nat.card F₁ ∧ Nat.card F₂ = q ∧
    5 ≤ Nat.card F₁ ∧
    (Nat.card ↥(StatedSL 2 F₁)).factorization 2 = (Nat.card ↥(StatedSL 2 F₂)).factorization 2 ∧
    ∃ K : Subgroup X, K ≤ C₁ ∧ (K.subgroupOf C₁).index = 2 ∧ IsCentralProductOfSL2 K F₁ F₂

@[expose] def HasSL2ProductOfIndexTwoCh6 (C₁ : Subgroup X) (q : ℕ) : Prop :=
  ∃ (F F₁ F₂ : Type) (_ : Field F) (_ : Field F₁) (_ : Field F₂) (_ : Finite F) (_ : Finite F₁)
    (_ : Finite F₂),
    Nat.card F = q ∧ Odd (Nat.card F₁) ∧ Odd (Nat.card F₂) ∧ Nat.card F₂ ≤ Nat.card F₁ ∧
    5 ≤ Nat.card F₁ ∧
    (Nat.card ↥(StatedSL 2 F₁)).factorization 2 = (Nat.card ↥(StatedSL 2 F)).factorization 2 ∧
    (Nat.card ↥(StatedSL 2 F₂)).factorization 2 = (Nat.card ↥(StatedSL 2 F)).factorization 2 ∧
    ∃ K : Subgroup X, K ≤ C₁ ∧ (K.subgroupOf C₁).index = 2 ∧ IsCentralProductOfSL2 K F₁ F₂

end Helpers

@[expose] def fixedSubgroup (Q : Type*) [Group Q] (φ : MulAut Q) : Subgroup Q :=
  MonoidHom.eqLocus φ.toMonoidHom (MonoidHom.id Q)

@[expose] def HasSolvableTwoComponentSL23 (X : Type*) [Group X] : Prop :=
  ∃ W : Subgroup (X ⧸ pPrimeCore 2 X), W.IsSubnormal ∧
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 3 ∧ Nonempty (↥W ≃* StatedSL 2 F)

@[expose] def IsFAutomorphism (Q : Type) [Group Q] (φ : MulAut Q) : Prop :=
  IsQuasisimple Q ∧ IsKGroupNative Q ∧ pRank 2 Q = 1 ∧ (∃ k : ℕ, orderOf φ = 2 ^ k) ∧
    ((∃ L : Subgroup ↥(fixedSubgroup Q φ), IsPComponent 2 L) ∨
      HasSolvableTwoComponentSL23 ↥(fixedSubgroup Q φ))

@[expose] def InducesFAut {G : Type} [Group G] (x : G) (K : Subgroup G) : Prop :=
  ∃ hx : x ∈ normalizer (K : Set G),
    IsFAutomorphism (↥K ⧸ pPrimeCore 2 ↥K) (inducedQuotAut K (pPrimeCore 2 ↥K) ⟨x, hx⟩)

@[expose] def IsRigidRankOneComp {G : Type*} [Group G] (z : G) (K : Subgroup G) : Prop :=
  IsPRigid 2 z K ∧ pRank 2 ↥K = 1

@[expose] def rigidProduct {G : Type*} [Group G] (z : G) : Subgroup G :=
  sSup {K | IsRigidRankOneComp z K}

@[expose] def rigidSectionCentralizer {G : Type*} [Group G] (z : G) : Subgroup G :=
  centralizerSection (rigidProduct z) (pPrimeCoreOf 2 (rigidProduct z))

@[expose] def IsStronglyClassicalInvolution (G : Type) [Group G] (z : G) : Prop :=
  orderOf z = 2 ∧ ∀ t : G, t ∈ centralizer ({z} : Set G) → IsConj z t →
    t ∉ zStar (rigidProduct z) →
      (Set.ncard {K : Subgroup G | IsRigidRankOneComp z K} = 1 ∨
        Set.ncard {K : Subgroup G | IsRigidRankOneComp z K} = 2) ∧
      CFSG.ABGLocalTools.IsSylowOf 2 (zpowers z) (zStar (rigidProduct z)) ∧
      (∀ K : Subgroup G, IsRigidRankOneComp z K →
        pRank 2 ↥(centralizer ({z, t} : Set G) ⊓ centralizerSection K (pPrimeCoreOf 2 K)) = 1) ∧
      (∃ S : Sylow 2 G, ∀ g : G,
        (g ∈ (S : Subgroup G) ∧ (∀ s ∈ (S : Subgroup G), s * g = g * s) ∧ g ^ 2 = 1) ↔
          g ∈ zpowers z) ∧
      (∀ K : Subgroup G, IsRigidRankOneComp z K → ¬ InducesFAut t K) ∧
      (Set.ncard {K : Subgroup G | IsRigidRankOneComp z K} = 1 →
        ∀ P : Sylow 2 ↥(rigidSectionCentralizer z),
          IsCyclic ↥P.toSubgroup ∨ IsNonabelianMaximalClassTwoGroup ↥P.toSubgroup)

@[expose] def IsReeGroup (Gs : Type) [Group Gs] : Prop := ∃ f : ℕ, LieModel Gs .twistedG2 0 3 f


@[expose] def IsTwoCentralG2Type (G : Type) [Group G] (Gs : Type) [Group Gs] : Prop :=
  (IsReeGroup Gs ∨ ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ LieModel Gs .G2 0 p f) ∧
    (∃ (S : Sylow 2 G) (S' : Sylow 2 Gs),
      Nonempty (↥(S : Subgroup G) ≃* ↥(S' : Subgroup Gs))) ∧
    ∃ z : G, IsCentralInvolution z ∧
      (∀ u : G, orderOf u = 2 → IsConj z u) ∧
      pPrimeCore 2 ↥(centralizer ({z} : Set G)) = ⊥ ∧
      ((IsReeGroup Gs ∧
          ∃ K : Subgroup ↥(centralizer ({z} : Set G)),
            IsInternalDirectProduct (zpowers (zElt z)) K
              (oPrimeResidual 2 ↥(centralizer ({z} : Set G))) ∧
            ∃ p f : ℕ, p.Prime ∧ (p ^ f % 8 = 3 ∨ p ^ f % 8 = 5) ∧ 5 ≤ p ^ f ∧
              LieModel ↥K .PSL 2 p f) ∨
        (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ LieModel Gs .G2 0 p f ∧
          HasSL2ProductOfIndexTwoCh6 (oPrimeResidual 2 ↥(centralizer ({z} : Set G))) (p ^ f)))

@[expose] def layerTimesSylow {X : Type*} [Group X] (z : X) (S : Subgroup X) : Subgroup X :=
  (layer ↥(centralizer ({z} : Set X))).map (centralizer ({z} : Set X)).subtype ⊔ S


@[expose] def maximalOverCentralizer {X : Type*} [Group X] (z : X) : Set (Subgroup X) :=
  {M | IsCoatom M ∧ centralizer ({z} : Set X) ≤ M}


theorem SameInvolutionFusionPattern.refl (G : Type*) [Group G] [Finite G] :
    SameInvolutionFusionPattern G G := by
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 2 G))
  exact ⟨S, S, MulEquiv.refl _, fun _ _ _ _ => Iff.rfl⟩

theorem SameCentralizerOfInvolutionPattern.refl (G : Type*) [Group G] [Finite G] :
    SameCentralizerOfInvolutionPattern G G := by
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 2 G))
  exact ⟨S, S, MulEquiv.refl _, fun _ _ _ _ => Iff.rfl, fun _ _ => ⟨MulEquiv.refl _⟩⟩

theorem IsApproxTo.refl (G : Type) [Group G] [Finite G] : IsApproxTo G G :=
  ⟨SameCentralizerOfInvolutionPattern.refl G, fun _ => rfl⟩

end CFSG.GH74.GLS
