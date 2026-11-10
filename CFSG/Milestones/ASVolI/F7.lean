module

public import CFSG.Quasithin.Background.RonanF713Main
public import CFSG.Quasithin.Background.F7TwoInvSQTKProved
public import CFSG.Quasithin.Background.F7TwoClaimC

public section

namespace CFSG.ASVolI.ChF

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.CosetGeom CFSG.Quasithin.F7
open scoped Pointwise

structure HypF_7_1 {G : Type} [Group G] (G₀ G₁ G₂ T : Subgroup G) : Prop where
  finite₁ : Finite G₁
  finite₂ : Finite G₂
  charTwo : CharTwo G₁
  sylow_inf : IsSylowTwoOf T (G₁ ⊓ G₂)
  sylow₁ : IsSylowTwoOf T G₁
  sylow₂ : IsSylowTwoOf T G₂
  gen : G₀ = G₁ ⊔ G₂
  o2_trivial : pCoreOf 2 G₀ = ⊥

structure HypF_7_6 {G : Type} [Group G] (G₀ G₁ G₂ T V : Subgroup G) : Prop where
  toHypF_7_1 : HypF_7_1 G₀ G₁ G₂ T
  reduced : IsTwoReducedIn G₁ V
  cT : T ⊓ Subgroup.centralizer (V : Set G) = pCoreOf 2 (G₁ ⊓ Subgroup.centralizer (V : Set G))

end CFSG.ASVolI.ChF

namespace CFSG.Quasithin.CosetGeom

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
open scoped Pointwise

variable {G : Type*} [Group G]

section Loc

variable {G₀ G₁ G₂ T V : Subgroup G}


end Loc

end CFSG.Quasithin.CosetGeom

namespace CFSG.ASVolI

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.CosetGeom CFSG.Quasithin.F7
open CFSG.ASVolI.ChF
open scoped Pointwise


@[expose] def F_7_3 : Prop :=
  ∀ (G : Type) [Group G] (G₀ G₁ G₂ T : Subgroup G), HypF_7_1 G₀ G₁ G₂ T →
    ∀ γ : CosetGeom G₀ G₁ G₂,
      (MulAction.orbit G₀ (γ₀ G₀ G₁ G₂) = Γ0 G₀ G₁ G₂ ∧
        MulAction.orbit G₀ (γ₁ G₀ G₁ G₂) = Γ1 G₀ G₁ G₂ ∧
        Γ0 G₀ G₁ G₂ ∪ Γ1 G₀ G₁ G₂ = Set.univ ∧ Disjoint (Γ0 G₀ G₁ G₂) (Γ1 G₀ G₁ G₂)) ∧
      ((∀ u v : CosetGeom G₀ G₁ G₂, (graph G₀ G₁ G₂).Adj u v →
          ∃ g : G₀, g • ({γ₀ G₀ G₁ G₂, γ₁ G₀ G₁ G₂} : Set (CosetGeom G₀ G₁ G₂)) = {u, v}) ∧
        (∀ g : G₀, g • ({γ₀ G₀ G₁ G₂, γ₁ G₀ G₁ G₂} : Set (CosetGeom G₀ G₁ G₂)) =
            {γ₀ G₀ G₁ G₂, γ₁ G₀ G₁ G₂} ↔ (g : G) ∈ G₁ ⊓ G₂)) ∧
      (graph G₀ G₁ G₂).Connected ∧
      ((∀ x : G₀, (x : G) ∈ stab γ ↔ x • γ = γ) ∧ stab γ ≤ G₀ ∧
        (∀ g : G₀, stab (g • γ₀ G₀ G₁ G₂) = conjSub (g : G) G₁ ∧
          stab (g • γ₁ G₀ G₁ G₂) = conjSub (g : G) G₂) ∧
        stab (γ₀ G₀ G₁ G₂) = G₁ ∧ stab (γ₁ G₀ G₁ G₂) = G₂) ∧
      (∀ δ ∈ nbrs γ, ∀ δ' ∈ nbrs γ, ∃ g : G₀, (g : G) ∈ stab γ ∧ g • δ = δ') ∧
      (∀ n : ℕ, ballStab n γ ≤ stab γ ∧ ((ballStab n γ).subgroupOf (stab γ)).Normal) ∧
      ((ballStab 1 (γ₀ G₀ G₁ G₂) = coreIn (G₁ ⊓ G₂) G₁ ∧
          IsGreatest {N : Subgroup G | N ≤ G₁ ⊓ G₂ ∧ (N.subgroupOf G₁).Normal}
            (ballStab 1 (γ₀ G₀ G₁ G₂))) ∧
        (ballStab 1 (γ₁ G₀ G₁ G₂) = coreIn (G₁ ⊓ G₂) G₂ ∧
          IsGreatest {N : Subgroup G | N ≤ G₁ ⊓ G₂ ∧ (N.subgroupOf G₂).Normal}
            (ballStab 1 (γ₁ G₀ G₁ G₂)))) ∧
      (∃ n : ℕ, 0 < n ∧ ∀ δ : CosetGeom G₀ G₁ G₂, ballStab n δ = ⊥)


@[expose] def F_7_4 : Prop :=
  ∀ (G : Type) [Group G] (G₀ G₁ G₂ T : Subgroup G), HypF_7_1 G₀ G₁ G₂ T →
    ∀ β γ : CosetGeom G₀ G₁ G₂, γ ∈ nbrs β →
      pCoreOf 2 (stab β) ⊓ ballStab 1 γ ≤ pCoreOf 2 (stab β ⊓ stab γ) ⊓ ballStab 1 γ ∧
      pCoreOf 2 (stab β ⊓ stab γ) ⊓ ballStab 1 γ ≤ pCoreOf 2 (ballStab 1 γ)


@[expose] def F_7_5 : Prop :=
  ∀ (G : Type) [Group G] (G₀ G₁ G₂ T : Subgroup G), HypF_7_1 G₀ G₁ G₂ T →
    ∀ (α : CosetGeom G₀ G₁ G₂) (n : ℕ), 0 < n → ∀ γ ∈ ballLT n α, ∀ δ ∈ nbrs γ,
      pCoreOf 2 (ballStab n α) ≤ pCoreOf 2 (ballStab 1 γ) ∧
      pCoreOf 2 (ballStab n α) ≤ pCoreOf 2 (stab γ ⊓ stab δ)


@[expose] def F_7_7 : Prop :=
  ∀ (G : Type) [Group G] (G₀ G₁ G₂ T V : Subgroup G), HypF_7_6 G₀ G₁ G₂ T V →
    (oTwoPrime (G₁ ⊓ Subgroup.centralizer (V : Set G)) = pCoreOf 2 (ballStab 1 (γ₀ G₀ G₁ G₂)) ∧
      pCoreOf 2 (ballStab 1 (γ₀ G₀ G₁ G₂)) = pCoreOf 2 G₁) ∧
    (∀ α β : CosetGeom G₀ G₁ G₂, β ∈ nbrs α →
      pCoreOf 2 (stab α) = pCoreOf 2 (stab α ⊓ stab β) ⊓ ballStab 1 α)


@[expose] def F_7_8 : Prop :=
  ∀ (G : Type) [Group G] (G₀ G₁ G₂ T V : Subgroup G), HypF_7_6 G₀ G₁ G₂ T V → V ≠ ⊥ →
    IsGreatest {n : ℕ | 0 < n ∧ V ≤ ballStab n (γ₀ G₀ G₁ G₂)} (critDist G₀ G₁ G₂ V)


@[expose] def F_7_9 : Prop :=
  ∀ (G : Type) [Group G] (G₀ G₁ G₂ T V : Subgroup G), HypF_7_6 G₀ G₁ G₂ T V → V ≠ ⊥ →
    (∀ γ ∈ ballLT (critDist G₀ G₁ G₂ V) (γ₀ G₀ G₁ G₂), ∀ δ ∈ nbrs γ,
      V ≤ pCoreOf 2 (ballStab 1 γ) ∧ V ≤ pCoreOf 2 (stab γ ⊓ stab δ)) ∧
    (∃ α ∈ sphere (critDist G₀ G₁ G₂ V) (γ₀ G₀ G₁ G₂), ¬ V ≤ ballStab 1 α) ∧
    IsLeast {n : ℕ | ∃ γ ∈ sphere n (γ₀ G₀ G₁ G₂), ¬ V ≤ ballStab 1 γ} (critDist G₀ G₁ G₂ V) ∧
    (weakClosureW0 T V ≤ pCoreOf 2 G₂ → Even (critDist G₀ G₁ G₂ V))


@[expose] def F_7_10 : Prop :=
  ∀ (G : Type) [Group G] (G₀ G₁ G₂ T V : Subgroup G), HypF_7_6 G₀ G₁ G₂ T V → V ≠ ⊥ →
    2 ≤ critDist G₀ G₁ G₂ V →
      Vv V (γ₁ G₀ G₁ G₂) ≤ pCoreOf 2 G₂ ∧ IsPGroup 2 (Vv V (γ₁ G₀ G₁ G₂))


@[expose] def F_7_11 : Prop :=
  ∀ (G : Type) [Group G] (G₀ G₁ G₂ T V : Subgroup G) (hyp : HypF_7_6 G₀ G₁ G₂ T V), V ≠ ⊥ →
    ∀ γ : CosetGeom G₀ G₁ G₂, dist (γ₀ G₀ G₁ G₂) γ = critDist G₀ G₁ G₂ V →
      ¬ V ≤ ballStab 1 γ →
      (∀ n : ℕ, n ≤ critDist G₀ G₁ G₂ V → ∀ δ : CosetGeom G₀ G₁ G₂,
        ∀ p : (graph G₀ G₁ G₂).Walk (γ₀ G₀ G₁ G₂) δ, p.length = n → ∀ v ∈ p.support, V ≤ stab v) ∧
      (Even (critDist G₀ G₁ G₂ V) →
        (⁅V, Vv V γ⁆ ≠ ⊥ ∧ ⁅V, Vv V γ⁆ ≤ V ⊓ Vv V γ) ∧ Vv V γ ≤ G₁ ∧
          (¬ Vv V γ ≤ Subgroup.centralizer (V : Set G) ∧ ⁅⁅V, Vv V γ⁆, Vv V γ⁆ = ⊥)) ∧
      (∀ δ ∈ Γ0 G₀ G₁ G₂, dist (γ₀ G₀ G₁ G₂) δ < critDist G₀ G₁ G₂ V → ⁅V, Vv V δ⁆ = ⊥) ∧
      (2 < critDist G₀ G₁ G₂ V → frattini ↥(Vv V (γ₁ G₀ G₁ G₂)) = ⊥) ∧
      (2 ≤ critDist G₀ G₁ G₂ V → dist (γ₁ G₀ G₁ G₂) γ + 1 = critDist G₀ G₁ G₂ V →
        ∀ γ' ∈ nbrs γ, dist (γ₁ G₀ G₁ G₂) γ' + 2 = critDist G₀ G₁ G₂ V →
          Vv V (γ₁ G₀ G₁ G₂) ≤ pCoreOf 2 (stab γ' ⊓ stab γ)) ∧
      (3 ≤ critDist G₀ G₁ G₂ V → Odd (critDist G₀ G₁ G₂ V) →
        (∀ γ₂ ∈ nbrs (γ₁ G₀ G₁ G₂), dist γ₂ γ + 2 = critDist G₀ G₁ G₂ V →
          Vv V γ ≤ pCoreOf 2 (stab (γ₁ G₀ G₁ G₂) ⊓ stab γ₂)) ∧
        (dist (γ₁ G₀ G₁ G₂) γ + 1 = critDist G₀ G₁ G₂ V →
          ⁅Vv V (γ₁ G₀ G₁ G₂), Vv V γ⁆ ≤ Vv V (γ₁ G₀ G₁ G₂) ⊓ Vv V γ ∧
          ⁅⁅Vv V (γ₁ G₀ G₁ G₂), Vv V γ⁆, Vv V γ⁆ = ⊥ ∧
          ⁅⁅Vv V γ, Vv V (γ₁ G₀ G₁ G₂)⁆, Vv V (γ₁ G₀ G₁ G₂)⁆ = ⊥)) ∧
      ((¬ @IsFFModule ↥V (commGroupOfElemAbelian hyp.reduced.2.2.1) (autOn G₁ V)) →
        Odd (critDist G₀ G₁ G₂ V)) ∧
      (V ≤ pCoreOf 2 G₂ →
        (¬ @IsFFModule ↥V (commGroupOfElemAbelian hyp.reduced.2.2.1) (autOn G₁ V)) →
          IsElemAbelian 2 (conjClosure V G₂))


@[expose] def F_7_12 : Prop :=
  ∀ (G : Type) [Group G] (G₀ G₁ G₂ T V : Subgroup G), HypF_7_6 G₀ G₁ G₂ T V → V ≠ ⊥ →
    (¬ V ≤ pCoreOf 2 G₂ → critDist G₀ G₁ G₂ V = 1) ∧
    (V ≤ pCoreOf 2 G₂ →
      ¬ (∀ x ∈ Vv V (γ₁ G₀ G₁ G₂), ∀ y ∈ Vv V (γ₁ G₀ G₁ G₂), x * y = y * x) →
      critDist G₀ G₁ G₂ V = 2)


@[expose] def F_7_13 : Prop :=
  ∀ (G : Type) [Group G] (G₀ G₁ G₂ T V : Subgroup G), HypF_7_6 G₀ G₁ G₂ T V → V ≠ ⊥ →
    ∀ γ : CosetGeom G₀ G₁ G₂, dist (γ₀ G₀ G₁ G₂) γ = critDist G₀ G₁ G₂ V →
      ¬ V ≤ ballStab 1 γ → dist (γ₁ G₀ G₁ G₂) γ + 1 = critDist G₀ G₁ G₂ V →
      (3 ≤ critDist G₀ G₁ G₂ V ∧ Odd (critDist G₀ G₁ G₂ V)) →
      IsUniqueMaxOver G₂ T (G₂ ⊓ Subgroup.normalizer (V : Set G)) →
      E1.nParam G₂ = 1 →
      ∀ A : Subgroup G, A ≤ Vv V (γ₁ G₀ G₁ G₂) → ¬ A ≤ ballStab 1 γ →
        (∃ α ∈ nbrs γ, (A ⊓ Subgroup.normalizer (Vv V α : Set G)).relIndex A = 2) ∧
        (CFSG.SectionRank.IsSQTKCat ↥G₂ →
          ∃ α ∈ nbrs γ, (A ⊓ Subgroup.normalizer (Vv V α : Set G)).relIndex A = 2 ∧
            ∃ h : G, h ∈ stab γ ∧ conjSub h⁻¹ A ≤ stab α ∧
            ¬ IsPGroup 2 ↥(A ⊔ conjSub h⁻¹ A))

section F713


end F713

@[expose] def F_7_14 : Prop :=
  ∀ (G : Type) [Group G] (G₀ G₁ G₂ T V : Subgroup G), HypF_7_6 G₀ G₁ G₂ T V → V ≠ ⊥ →
    (weakClosureW0 T V ≤ pCoreOf 2 G₁ → critDist G₀ G₁ G₂ V % 2 = (0 + 1) % 2) ∧
    (weakClosureW0 T V ≤ pCoreOf 2 G₂ → critDist G₀ G₁ G₂ V % 2 = (1 + 1) % 2)


end CFSG.ASVolI
