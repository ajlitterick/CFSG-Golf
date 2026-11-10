module

public import CFSG.GH74.GLS.IVK.Defs

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup CFSG CFSG.GH74.GLS CFSG.GorensteinWalter
open scoped commutatorElement

structure ProdSL2 (H : Type) [Group H] (K₁ K₂ : Subgroup H) (F₁ F₂ : Type) [Field F₁] [Field F₂] :
    Prop where
  comm : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a
  iso₁ : Nonempty (↥K₁ ≃* SL2 F₁)
  iso₂ : Nonempty (↥K₂ ≃* SL2 F₂)
  card_inter : Nat.card ↥(K₁ ⊓ K₂) = 2
  fstar_normal : (K₁ ⊔ K₂).Normal
  fstar_centralizer : centralizer ((K₁ ⊔ K₂ : Subgroup H) : Set H) ≤ K₁ ⊔ K₂

@[expose] def IsDiagInv {H : Type} [Group H] (K₁ K₂ : Subgroup H) (F₁ F₂ : Type) [Field F₁]
    [Field F₂] (w : H) : Prop :=
  (∀ x ∈ K₁, w * x * w⁻¹ ∈ K₁) ∧ (∀ x ∈ K₂, w * x * w⁻¹ ∈ K₂) ∧
  (∃ _ : (K₁.subgroupOf (K₁ ⊔ K₂ ⊔ zpowers w)).Normal,
    Nonempty ((↥(K₁ ⊔ K₂ ⊔ zpowers w)) ⧸ (K₁.subgroupOf (K₁ ⊔ K₂ ⊔ zpowers w)) ≃* PGL2 F₂)) ∧
  (∃ _ : (K₂.subgroupOf (K₁ ⊔ K₂ ⊔ zpowers w)).Normal,
    Nonempty ((↥(K₁ ⊔ K₂ ⊔ zpowers w)) ⧸ (K₂.subgroupOf (K₁ ⊔ K₂ ⊔ zpowers w)) ≃* PGL2 F₁))

@[expose] def IVK_3_1a : Prop :=
  ∀ (F₁ F₂ : Type) [Field F₁] [Field F₂] (H : Type) [Group H] [Finite H] (K₁ K₂ : Subgroup H),
    ProdSL2 H K₁ K₂ F₁ F₂ → ∀ z ∈ K₁ ⊓ K₂, z ≠ 1 →
      ∀ x y : H, x ∈ K₁ ⊔ K₂ → y ∈ K₁ ⊔ K₂ → orderOf x = 2 → orderOf y = 2 → x ≠ z → y ≠ z →
        ConjUnder (K₁ ⊔ K₂) x y

@[expose] def IVK_3_1b : Prop :=
  ∀ (F₁ F₂ : Type) [Field F₁] [Field F₂] (H : Type) [Group H] [Finite H] (K₁ K₂ : Subgroup H),
    ProdSL2 H K₁ K₂ F₁ F₂ → ∀ z ∈ K₁ ⊓ K₂, z ≠ 1 → ∀ T : Sylow 2 H, ∀ t ∈ (T : Subgroup H),
      orderOf t = 2 → K₁.map (MulAut.conj t).toMonoidHom = K₂ →
        (∀ x : H, (∃ p ∈ (T : Subgroup H) ⊓ (K₁ ⊔ K₂), x = p * t) → orderOf x = 2 →
          ConjUnder (K₁ ⊔ K₂) x t ∨ ConjUnder (K₁ ⊔ K₂) x (z * t)) ∧
        Nonempty (↥(centralizer ({t} : Set H) ⊓ (K₁ ⊔ K₂)) ≃* L2 F₁ × Multiplicative (ZMod 2))

@[expose] def IVK_3_1c : Prop :=
  ∀ (F₁ F₂ : Type) [Field F₁] [Field F₂] (H : Type) [Group H] [Finite H] (K₁ K₂ : Subgroup H),
    ProdSL2 H K₁ K₂ F₁ F₂ → ∀ T : Sylow 2 H, ∀ w ∈ (T : Subgroup H), orderOf w = 2 →
      IsDiagInv K₁ K₂ F₁ F₂ w →
        (∀ x y : H, (∃ k ∈ K₁ ⊔ K₂, x = k * w) → (∃ k ∈ K₁ ⊔ K₂, y = k * w) →
          orderOf x = 2 → orderOf y = 2 → ConjUnder (K₁ ⊔ K₂) x y) ∧
        ∀ S : Sylow 2 ↥(centralizer ({w} : Set H) ⊓ (K₁ ⊔ K₂)), Nat.card ↥S = 4


end CFSG.GH74.GLS.IVK
