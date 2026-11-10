module

public import CFSG.GH74.GLS.IVK.Defs2
public import CFSG.GH74.GLS.IVK.Defs

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GorensteinWalter
open scoped commutatorElement

section Local

variable {K : Type} [Group K]

@[expose] def Ez (z : K) : Subgroup K :=
  (layer ↥(centralizer ({z} : Set K))).map (centralizer ({z} : Set K)).subtype

@[expose] def O2z (z : K) : Subgroup K :=
  (oResidual 2 ↥(centralizer ({z} : Set K))).map (centralizer ({z} : Set K)).subtype

end Local

@[expose] def IVK_4_4a : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (ε : ℤ) (p n : ℕ), p.Prime → p ≠ 2 →
    IsLnEps 3 K ε (p ^ n) → ∀ U : Subgroup K, IsFourSubgroup U → ∀ u ∈ U, ∀ u' ∈ U,
      orderOf u = 2 → orderOf u' = 2 → u ≠ u' →
        (3 < p ^ n → Subgroup.closure ((Ez u : Set K) ∪ (Ez u' : Set K)) = ⊤) ∧
        (p ^ n = 3 → Subgroup.closure ((O2z u : Set K) ∪ (O2z u' : Set K)) = ⊤)

@[expose] def IVK_4_4b : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (ε : ℤ) (p n : ℕ), p.Prime → p ≠ 2 →
    IsLnEps 3 K ε (p ^ n) → ∀ S : Sylow 2 K,
      (¬ ((p ^ n : ℕ) : ℤ) ≡ ε [ZMOD 4] → ∃ m : ℕ, IsSemidihedralTwoGroup ↥S m) ∧
      (((p ^ n : ℕ) : ℤ) ≡ ε [ZMOD 4] → ∃ m : ℕ, 2 ≤ m ∧ Nonempty (↥S ≃* Open.WreathedTwoGroup m))


@[expose] def IVK_4_10 : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (q : ℕ), Odd q → 5 ≤ q → IsSp4L4U4 K q →
    ∀ (P : Sylow 2 K) (z : K), z ∈ (P : Subgroup K) → orderOf z = 2 →
      (∀ x ∈ (P : Subgroup K), x * z = z * x) →
        ∃ (t w : K) (E₁ E₂ : Subgroup K), t ∈ (P : Subgroup K) ∧ w ∈ (P : Subgroup K) ∧
          orderOf t = 2 ∧ (w = 1 ∨ orderOf w = 2) ∧ Commute t w ∧
          (P : Subgroup K) = ((P : Subgroup K) ⊓ Ez z) ⊔ zpowers t ⊔ zpowers w ∧
          Ez z ⊓ (zpowers t ⊔ zpowers w) = ⊥ ∧
          IsConj z t ∧ Ez z = E₁ ⊔ E₂ ∧ E₂ = E₁.map (MulAut.conj t).toMonoidHom ∧
          HasSL2Model ↥E₁ (fun r => r = q) ∧ E₁ ⊓ E₂ = zpowers z ∧
          (∀ a ∈ E₁, ∀ b ∈ E₂, a * b = b * a) ∧
          normalizer (E₁ : Set K) ⊓ (P : Subgroup K) = ((P : Subgroup K) ⊓ Ez z) ⊔ zpowers w ∧
          (w = 1 ↔ IsPSp4 K q) ∧
          (∀ x : K, orderOf x = 2 → IsConj z x ∨ IsConj (t * z) x) ∧ ¬ IsConj z (t * z) ∧
          (∀ x ∈ Ez z, orderOf x = 2 → x ≠ z → IsConj (t * z) x) ∧
          (w ≠ 1 → ∀ Ei ∈ ({E₁, E₂} : Set (Subgroup K)),
            ∃ _ : ((zpowers z).subgroupOf (Ei ⊔ zpowers w)).Normal,
              IsPGL2 (↥(Ei ⊔ zpowers w) ⧸ (zpowers z).subgroupOf (Ei ⊔ zpowers w))
                (fun r => r = q)) ∧
          (w ≠ 1 → IsConj z (t * w) ∧
            ∀ x ∈ (P : Subgroup K) ⊓ Ez z, orderOf (x * w) = 2 → IsConj z (x * w)) ∧
          ∀ y : K, IsCentralInvolution y → IsConj z y


end CFSG.GH74.GLS.IVK
