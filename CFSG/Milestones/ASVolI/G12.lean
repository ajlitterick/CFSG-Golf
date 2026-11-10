module

public import CFSG.Quasithin.Background.G12Final
public import CFSG.Foundations.HigherElementaryThompson

public section

namespace CFSG.ASVolI.ChG

open CFSG.Quasithin CFSG.Quasithin.G11 CFSG.Open

section Vocab

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] def Qv (B : LinearMap.BilinForm (ZMod 2) V) (G : Subgroup (GLV V)) (v : V) :
    Subgroup (GLV V) :=
  QSub G v (perp B v)

@[expose] def QFaithfulOnW (B : LinearMap.BilinForm (ZMod 2) V) (G : Subgroup (GLV V)) (v : V) :
    Prop :=
  ∀ x ∈ Qv B G v, (∀ w ∈ perp B v, x w = w) → x = 1

@[expose] def TransOnNonzero (G : Subgroup (GLV V)) : Prop :=
  ∀ x y : V, x ≠ 0 → y ≠ 0 → ∃ g ∈ G, g x = y

@[expose] def IsRegularAt (Y : Subgroup (GLV V)) (x : V) : Prop :=
  ∀ g ∈ Y, g x = x → g = 1

@[expose] def FullAxisTransvOnQuot (B : LinearMap.BilinForm (ZMod 2) V) (v : V)
    (Y : Subgroup (GLV V)) : Prop :=
  (∀ y ∈ Y, ∃ c ∈ perp B v, ∀ x : V, y x - x - B x v • c ∈ Submodule.span (ZMod 2) {v}) ∧
  ∀ c ∈ perp B v, ∃ y ∈ Y, ∀ x : V, y x - x - B x v • c ∈ Submodule.span (ZMod 2) {v}

@[expose] def spStab (B : LinearMap.BilinForm (ZMod 2) V) (v : V) : Subgroup (GLV V) :=
  spSub B ⊓ MulAction.stabilizer (GLV V) v

@[expose] def IsQuadFormFor (B : LinearMap.BilinForm (ZMod 2) V) (q : V → ZMod 2) : Prop :=
  ∀ x y : V, q (x + y) = q x + q y + B x y

@[expose] def Concl121 (B : LinearMap.BilinForm (ZMod 2) V) (G : Subgroup (GLV V)) (v : V) : Prop :=
  G = spSub B ∨
  (∃ q : V → ZMod 2, IsQuadFormFor B q ∧ (G = orthSub q ∨ G = omegaSub B q) ∧
    ∀ w : V, (∃ g ∈ G, w = g v) ↔ (w ≠ 0 ∧ q w = 0)) ∨
  (Module.finrank (ZMod 2) V = 4 ∧
    (G = ⁅spSub B, spSub B⁆ ∨
      (Nonempty (↥G ≃* Equiv.Perm (Fin 5)) ∧
        ∃ A : Subgroup (GLV V), A ≤ G ∧ IsL24ModuleFor A)))

structure HypG121 (B : LinearMap.BilinForm (ZMod 2) V) (G : Subgroup (GLV V)) (u v : V) :
    Prop where
  symp : IsSymplectic B
  le_sp : G ≤ spSub B
  u_mem : IsStarVec B G u
  v_mem : IsStarVec B G v
  uv : B u v ≠ 0
  dim : 4 ≤ Module.finrank (ZMod 2) V

structure MinCx (B : LinearMap.BilinForm (ZMod 2) V) (G : Subgroup (GLV V)) (u v : V) : Prop where
  hyp : HypG121 B G u v
  u_mem : u ∈ orbitSet G v
  not_concl : ¬ Concl121 B G v
  minimal : ∀ (V' : Type) [AddCommGroup V'] [Module (ZMod 2) V'] [Finite V']
    (B' : LinearMap.BilinForm (ZMod 2) V') (G' : Subgroup (GLV V')) (u' v' : V'),
    HypG121 B' G' u' v' → Module.finrank (ZMod 2) V' < Module.finrank (ZMod 2) V →
      Concl121 B' G' v'

open Classical in
@[expose] noncomputable def qOrb (G : Subgroup (GLV V)) (v : V) : V → ZMod 2 :=
  fun z => if z = 0 ∨ z ∈ orbitSet G v then 0 else 1

@[expose] def IsNonsingPair (B : LinearMap.BilinForm (ZMod 2) V) (G : Subgroup (GLV V)) (v : V)
    (e : ZMod 2) (x y : V) : Prop :=
  qOrb G v x = 1 ∧ qOrb G v y = 1 ∧ x ≠ y ∧ B x y = e

end Vocab

section Hat

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
  {Û : Type} [AddCommGroup Û] [Module (ZMod 2) Û]

structure HatModel (B : LinearMap.BilinForm (ZMod 2) V) (w : V) (π : ↥(perp B w) →ₗ[ZMod 2] Û) :
    Prop where
  surj : Function.Surjective π
  ker : ∀ x : ↥(perp B w), π x = 0 ↔ ((x : V) = 0 ∨ (x : V) = w)

open Classical in
@[expose] noncomputable def hatOf (B : LinearMap.BilinForm (ZMod 2) V) (w : V)
    (π : ↥(perp B w) →ₗ[ZMod 2] Û) (x : V) : Û :=
  if h : x ∈ perp B w then π ⟨x, h⟩ else 0

@[expose] def HatForm (B : LinearMap.BilinForm (ZMod 2) V) (w : V) (π : ↥(perp B w) →ₗ[ZMod 2] Û)
    (B' : LinearMap.BilinForm (ZMod 2) Û) : Prop :=
  ∀ x y : ↥(perp B w), B' (π x) (π y) = B (x : V) (y : V)

@[expose] def Gstar (B : LinearMap.BilinForm (ZMod 2) V) (G : Subgroup (GLV V)) (w : V)
    (π : ↥(perp B w) →ₗ[ZMod 2] Û) : Subgroup (GLV Û) :=
  Subgroup.closure {φ : GLV Û | ∃ g ∈ G, g w = w ∧
    ∀ x y : ↥(perp B w), g (x : V) = (y : V) → φ (π x) = π y}

@[expose] def HatQuadProp (B : LinearMap.BilinForm (ZMod 2) V) (G : Subgroup (GLV V)) (v w : V)
    (π : ↥(perp B w) →ₗ[ZMod 2] Û) (B' : LinearMap.BilinForm (ZMod 2) Û) (qw : Û → ZMod 2) : Prop :=
  IsQuadFormFor B' qw ∧
  (Gstar B G w π = orthSub qw ∨ Gstar B G w π = omegaSub B' qw) ∧
  {z : Û | z ≠ 0 ∧ qw z = 0} = {z : Û | ∃ g ∈ G, g w = w ∧ z = hatOf B w π (g v)}

end Hat

end CFSG.ASVolI.ChG

namespace CFSG.ASVolI

open CFSG.Quasithin CFSG.Quasithin.G11 CFSG.Open CFSG.ASVolI.ChG

@[expose] def G_12_1 : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (G : Subgroup (GLV V)) (u v : V),
    HypG121 B G u v → Concl121 B G v


@[expose] def G_12_2 : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (G : Subgroup (GLV V)) (u v : V),
    HypG121 B G u v →
      (∀ x ∈ Qv B G v, x ≠ 1 → ∀ y : V, x y = y → y ∈ perp B v) ∧
      ((QFaithfulOnW B G v ∧ pRank 2 (Qv B G v) = Module.finrank (ZMod 2) V - 2) ∨
        (Qv B G v = pCoreOf 2 (spStab B v) ∧
          pRank 2 (Qv B G v) = Module.finrank (ZMod 2) V - 1 ∧
          ∃ t ∈ Qv B G v, ∀ x : V, t x = x + B x v • v)) ∧
      FullAxisTransvOnQuot B v (Qv B G v)

private instance g12h2_finite_glv {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V] :
    Finite (GLV V) :=
  Finite.of_injective _ DFunLike.coe_injective


@[expose] def G_12_3 : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (G : Subgroup (GLV V)) (u v : V),
    HypG121 B G u v →
      IsIrr (Qv B G v ⊔ Qv B G u) ⊤ ∧
      ∃ g ∈ Qv B G v ⊔ Qv B G u, g v ∉ perp B v


@[expose] def G_12_4 : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (G : Subgroup (GLV V)) (u v : V),
    HypG121 B G u v →
      ((∀ x : V, x ∉ perp B v → x ∈ orbitSet G v) → TransOnNonzero G) ∧
      ((∀ x : V, x ∈ perp B v → x ≠ 0 → x ∈ orbitSet G v) → TransOnNonzero G)


@[expose] def G_12_5 : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (G : Subgroup (GLV V)) (u v : V),
    HypG121 B G u v → ¬ QFaithfulOnW B G v → G = spSub B


@[expose] def G_12_6 : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (G : Subgroup (GLV V)) (u v : V),
    HypG121 B G u v → QFaithfulOnW B G v →
      ((∀ x : V, x ∉ perp B v →
          x ∈ orbitSet (Qv B G v) u ∨ x ∈ orbitSet (Qv B G v) (u + v)) ∧
        u + v ∉ orbitSet (Qv B G v) u ∧
        IsRegularAt (Qv B G v) u ∧ IsRegularAt (Qv B G v) (u + v)) ∧
      (∀ w : V, w ∈ perp B v → w ≠ 0 → w ≠ v →
        w ∈ orbitSet (Qv B G v) (v + w) ∧ (w ∈ orbitSet G v ↔ w + v ∈ orbitSet G v)) ∧
      (TransOnNonzero G ∨ Xor (u ∈ orbitSet G v) (u + v ∈ orbitSet G v))


@[expose] def G_12_7 : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (G : Subgroup (GLV V)) (u v : V),
    MinCx B G u v → Module.finrank (ZMod 2) V = 4 → ¬ TransOnNonzero G


@[expose] def G_12_8 : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (G : Subgroup (GLV V)) (u v : V),
    MinCx B G u v →
    ∀ w : V, w ∈ perp B v → w ∈ orbitSet G v → w ≠ v →
    ∀ (Û : Type) [AddCommGroup Û] [Module (ZMod 2) Û] (π : ↥(perp B w) →ₗ[ZMod 2] Û),
      HatModel B w π →
      ∃ B' : LinearMap.BilinForm (ZMod 2) Û, HatForm B w π B' ∧
        (IsSymplectic B' ∧ Gstar B G w π ≤ spSub B') ∧
        (∃ u' : V, u' ∈ orbitSet G v ∧ u' ∈ perp B w ∧ u' ∉ perp B v) ∧
        (∀ u' : V, u' ∈ orbitSet G v → u' ∈ perp B w → u' ∉ perp B v →
          IsStarVec B' (Gstar B G w π) (hatOf B w π v) ∧
            IsStarVec B' (Gstar B G w π) (hatOf B w π u')) ∧
        (4 < Module.finrank (ZMod 2) V →
          ∃ qw : Û → ZMod 2, HatQuadProp B G v w π B' qw) ∧
        (4 < Module.finrank (ZMod 2) V → ∀ qw : Û → ZMod 2, HatQuadProp B G v w π B' qw →
          ∀ z : V, z ∈ perp B w → z ≠ 0 → z ≠ w →
            (z ∈ orbitSet G v ↔ qw (hatOf B w π z) = 0))


@[expose] def G_12_9 : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (G : Subgroup (GLV V)) (u v : V),
    MinCx B G u v → ¬ TransOnNonzero G


@[expose] def G_12_10 : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (G : Subgroup (GLV V)) (u v : V),
    MinCx B G u v →
    (∀ x y : V, qOrb G v (x + y) = qOrb G v x + qOrb G v y + B x y) →
      (∃ Q : QuadraticMap (ZMod 2) V (ZMod 2), (∀ x, Q x = qOrb G v x) ∧
        ∀ x y, QuadraticMap.polar Q x y = B x y) ∧
      (G = orthSub (qOrb G v) ∨ G = omegaSub B (qOrb G v))


@[expose] def G_12_11 : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (G : Subgroup (GLV V)) (u v : V),
    MinCx B G u v →
      (∀ x y : V, qOrb G v x = 1 → qOrb G v y = 1 → ∃ g ∈ G, g x = y) ∧
      4 < Module.finrank (ZMod 2) V ∧
      ∀ e : ZMod 2,
        (∀ x y x' y' : V, IsNonsingPair B G v e x y → IsNonsingPair B G v e x' y' →
          ∃ g ∈ G, Submodule.map (g : V →ₗ[ZMod 2] V) (Submodule.span (ZMod 2) {x, y}) =
            Submodule.span (ZMod 2) {x', y'}) ∧
        (∀ x y : V, IsNonsingPair B G v e x y → qOrb G v (x + y) = e)


@[expose] def G_12_12 : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (H K Q : Subgroup (GLV V)) (W : Submodule (ZMod 2) V) (v : V),
    2 < Module.finrank (ZMod 2) V →
    K ≤ H → (∀ h ∈ H, ∀ k ∈ K, h * k * h⁻¹ ∈ K) → IsIrr K ⊤ → SelfDual K ⊤ →
    Q ≤ H → (∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a) → (∀ a ∈ Q, a * a = 1) →
    Module.finrank (ZMod 2) W + 1 = Module.finrank (ZMod 2) V →
    ∀ (hv : v ∈ W), v ≠ 0 → FullTransvections Q W v hv →
      ∃ f : LinearMap.BilinForm (ZMod 2) V,
        (IsSymplectic f ∧ K ⊔ Q ≤ spSub f) ∧
        W = perp f v ∧
        ((∀ k ∈ K, IsStarVec f (K ⊔ Q) (k v)) ∧ ∃ h ∈ H, h v ∉ W) ∧
        (H ≤ spSub f ∨ ∃ ω : GLV V, (∀ x, ω (ω x) + ω x + x = 0) ∧
          H = Subgroup.normalizer (Subgroup.zpowers ω : Set (GLV V))) ∧
        (Concl121 f (K ⊔ Q) v ∧ (H ≤ spSub f → Concl121 f H v))


end CFSG.ASVolI
