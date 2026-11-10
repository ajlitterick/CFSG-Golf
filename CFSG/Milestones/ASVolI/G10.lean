module

public import CFSG.Quasithin.Background.G10Basic
import CFSG.Quasithin.Background.G10Fourteen
import CFSG.Quasithin.Background.G105Core
import CFSG.Quasithin.Background.RonanG1016Final
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.G10Stmts
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.ASVolI.ChG

open CFSG.Quasithin CFSG.Quasithin.G11 CFSG.Open

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] def IsSemisimpleFor (K : Subgroup (GLV V)) : Prop :=
  ∀ U : Submodule (ZMod 2) V, Invariant K U → ∃ U' : Submodule (ZMod 2) V, Invariant K U' ∧ IsCompl U U'

@[expose] def InducesIsometries (K : Subgroup (GLV V)) (I : Submodule (ZMod 2) V)
    (f : LinearMap.BilinForm (ZMod 2) I) : Prop :=
  (∀ k ∈ K, ∀ x y x' y' : I, k (x : V) = (x' : V) → k (y : V) = (y' : V) → f x' y' = f x y) ∧
    ∀ g : I ≃ₗ[ZMod 2] I, (∀ x y, f (g x) (g y) = f x y) → ∃ k ∈ K, ∀ i : I, k (i : V) = ((g i : I) : V)

@[expose] def InducesSp (K : Subgroup (GLV V)) (I : Submodule (ZMod 2) V) : Prop :=
  ∃ f : LinearMap.BilinForm (ZMod 2) I, (∀ x, f x x = 0) ∧ (∀ x, (∀ y, f x y = 0) → x = 0) ∧
    InducesIsometries K I f

@[expose] def InducesOrth (K : Subgroup (GLV V)) (I : Submodule (ZMod 2) V) : Prop :=
  ∃ q : I → ZMod 2, (∀ (c : ZMod 2) x, q (c • x) = c * c * q x) ∧
    (∃ B' : LinearMap.BilinForm (ZMod 2) I, (∀ x y, q (x + y) = q x + q y + B' x y) ∧
      (∀ x, (∀ y, B' x y = 0) → x = 0)) ∧
    (∀ k ∈ K, ∀ x x' : I, k (x : V) = (x' : V) → q x' = q x) ∧
    ∀ g : I ≃ₗ[ZMod 2] I, (∀ x, q (g x) = q x) → ∃ k ∈ K, ∀ i : I, k (i : V) = ((g i : I) : V)

@[expose] def IsSymNaturalSub (K : Subgroup (GLV V)) (I : Submodule (ZMod 2) V) (n : ℕ) : Prop :=
  ∃ (φ : ↥K ≃* Equiv.Perm (Fin n)) (β : ↥(permCore n) →ₗ[ZMod 2] ↥I),
    Function.Surjective β ∧
    (∀ u : ↥(permCore n), β u = 0 ↔ (u = 0 ∨ (Even n ∧ ∀ i, (u : Fin n → ZMod 2) i = 1))) ∧
    ∀ (γ : ↥K) (u u' : ↥(permCore n)),
      (u' : Fin n → ZMod 2) = permAct (φ γ) (u : Fin n → ZMod 2) →
        ((β u' : I) : V) = (γ : GLV V) ((β u : I) : V)

end CFSG.ASVolI.ChG

namespace CFSG.ASVolI

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.G11 CFSG.ASVolI.ChG
open scoped commutatorElement

@[expose] def G_10_2 : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ : Subgroup (GLV V)), G101Hyp B Γ v₁ W X X₀ →
      Module.finrank (ZMod 2) V ≤ 2 * (Nat.log 2 (X₀.relIndex X) + 1) ∧
        2 * (Nat.log 2 (X₀.relIndex X) + 1) ≤ 2 * (CFSG.Open.pRank 2 Γ + 1)


@[expose] def G_10_3 : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ : Subgroup (GLV V)), G101Hyp B Γ v₁ W X X₀ →
      (∀ U : Submodule (ZMod 2) V, U ≠ ⊥ → Invariant Γ U → TwoReducedOn Γ U) ∧ pCoreOf 2 Γ = ⊥


@[expose] def G_10_4 : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ : Subgroup (GLV V)), G101Hyp B Γ v₁ W X X₀ →
      ∀ H : Subgroup (GLV V), H ≤ Γ → (∀ γ ∈ Γ, ∀ h ∈ H, γ * h * γ⁻¹ ∈ H) → H ≠ ⊥ →
      ∀ U : Submodule (ZMod 2) V, U ≠ ⊥ → U ≠ ⊤ → IsIrr (H ⊔ X) U →
        (H = Γ ∨ (v₁ ∉ U ∧ commSpace X U ≠ ⊥)) →
          Module.finrank (ZMod 2) V = 4 ∧ Module.finrank (ZMod 2) U = 2 ∧ Group.IsSolvable ↥Γ

theorem as_G_10_4 : G_10_4 :=
  CFSG.Quasithin.g10_4 CFSG.Quasithin.G11.g10_3 CFSG.Quasithin.G11.SzG11S.b49

@[expose] def G_10_5 : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ : Subgroup (GLV V)), G101Hyp B Γ v₁ W X X₀ →
      IsIrr Γ ⊤ ∨
        (Module.finrank (ZMod 2) V = 4 ∧
          ((Nonempty (↥Γ ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) ∧
              Γ = Subgroup.closure {g | g ∈ Γ ∧ ∃ c : V, InducesTransvection g ⊤ c}) ∨
            (IsElemAbelian 3 (pCoreOf 3 Γ) ∧ Nat.card ↥(pCoreOf 3 Γ) = 9 ∧
              ∃ t ∈ Γ, t * t = 1 ∧ t ≠ 1 ∧ Γ = pCoreOf 3 Γ ⊔ Subgroup.zpowers t ∧
                ∀ x ∈ pCoreOf 3 Γ, t * x * t⁻¹ = x⁻¹)))


@[expose] def G_10_7 : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ L : Subgroup (GLV V)),
    IsIrr Γ ⊤ → IsComponentOf L Γ → (∃ x ∈ X, ∃ l ∈ L, x * l ≠ l * x) →
    G101Hyp B Γ v₁ W X X₀ →
      fixedSpace (normalClosure Γ L) = ⊥ ∧ commSpace (normalClosure Γ L) ⊤ = ⊤ ∧
      ∀ I : Submodule (ZMod 2) V, IrrPlus (normalClosure Γ L) I →
        (IsIrr (normalClosure Γ L) I ∧
          (∀ γ ∈ Γ, conjSub γ I = I ∨ conjSub γ I ⊓ I = ⊥) ∧ IsSemisimpleFor (normalClosure Γ L)) ∧
        (Isotropic B I ∨ NondegOn B I) ∧
        (∃ (k : ℕ) (Is : Fin k → Submodule (ZMod 2) V), (∃ h : 0 < k, Is ⟨0, h⟩ = I) ∧
          (∀ i, IrrPlus (normalClosure Γ L) (Is i)) ∧ iSupIndep Is ∧ (⨆ i, Is i) = ⊤ ∧
          ((NondegOn B I ∧ B.orthogonal I = ⨆ i : {i : Fin k // 0 < i.val}, Is i) ∨
            (Isotropic B I ∧ ∃ h : 1 < k, IsDualOf (normalClosure Γ L) I (Is ⟨1, h⟩) ∧
              NondegOn B (I ⊔ Is ⟨1, h⟩) ∧
              B.orthogonal (I ⊔ Is ⟨1, h⟩) = ⨆ i : {i : Fin k // 2 ≤ i.val}, Is i))) ∧
        2 < Module.finrank (ZMod 2) I

section G107

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]


end G107


@[expose] def G_10_9 : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ L : Subgroup (GLV V)), G108Hyp B Γ v₁ W X X₀ L →
      ∀ T : Subgroup (GLV V),
        IsSylowTwoOf T (Γ ⊓ MulAction.stabilizer (V ≃ₗ[ZMod 2] V) v₁) →
        X ≤ T → T ≤ Subgroup.normalizer (X : Set (GLV V)) →
          IsSylowTwoOf T Γ ∧ ⁅X, T ⊓ normalClosure Γ L⁆ ≤ X ⊓ normalClosure Γ L ∧
            IsElemAbelian 2 ⁅X, T ⊓ normalClosure Γ L⁆


@[expose] def G_10_10 : Prop := G1010Stmt

theorem as_G_10_10 : G_10_10 :=
  CFSG.Quasithin.G11.g10_10_of_g10_4 as_G_10_4

@[expose] def G_10_11 : Prop := G1011Stmt

theorem as_G_10_11 : G_10_11 := CFSG.Quasithin.G11.g10_11 as_G_10_10

@[expose] def G_10_12 : Prop := G1012Stmt

theorem as_G_10_12 : G_10_12 := CFSG.Quasithin.G11.g10_12 as_G_10_11

@[expose] def G_10_13 : Prop := G1013Stmt


@[expose] def G_10_14 : Prop := G1014Stmt

theorem as_G_10_14 : G_10_14 := CFSG.Quasithin.G11.g10_14 as_G_10_12

@[expose] def G_10_15 : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ L : Subgroup (GLV V)), G108Hyp B Γ v₁ W X X₀ L →
      G1015Concl B Γ v₁ W X L


@[expose] def G_10_16 : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ L : Subgroup (GLV V)), G108Hyp B Γ v₁ W X X₀ L →
      ∀ a ∈ X, a ≠ 1 → Module.finrank (ZMod 2) (LinearMap.range (a.toLinearMap - LinearMap.id)) ≤ 2 →
        (∃ h ∈ normalClosure Γ L, a * h ≠ h * a) ∧
        (∀ I : Submodule (ZMod 2) V, IrrPlus (normalClosure Γ L) I → conjSub a I = I) ∧
        (normalClosure Γ L ≤ normalClosure Γ (Subgroup.zpowers a) ∧
          ∀ I : Submodule (ZMod 2) V, IrrPlus (normalClosure Γ L) I ↔
            IrrPlus (normalClosure Γ (Subgroup.zpowers a)) I) ∧
        (IsIrr (normalClosure Γ L) ⊤ ∨
          ∃ I₁ I₂ : Submodule (ZMod 2) V, IsCompl I₁ I₂ ∧
            Invariant (normalClosure Γ L ⊔ Subgroup.zpowers a) I₁ ∧
            Invariant (normalClosure Γ L ⊔ Subgroup.zpowers a) I₂ ∧
            (HIso (normalClosure Γ L ⊔ Subgroup.zpowers a) I₁ I₂ ∨
              (Module.finrank (ZMod 2) I₁ = 4 ∧ AutAll (normalClosure Γ L) I₁)) ∧
            (∃ c₁ : V, InducesTransvection a I₁ c₁) ∧ (∃ c₂ : V, InducesTransvection a I₂ c₂) ∧
            (InducesSp (normalClosure Γ L ⊔ Subgroup.zpowers a) I₁ ∨
              InducesOrth (normalClosure Γ L ⊔ Subgroup.zpowers a) I₁ ∨
              (∃ n : ℕ, IsSymNaturalSub (normalClosure Γ L ⊔ Subgroup.zpowers a) I₁ n) ∨
              (Module.finrank (ZMod 2) I₁ = 4 ∧ AutAll (normalClosure Γ L) I₁)))


end CFSG.ASVolI
