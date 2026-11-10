module

public import CFSG.GH74.GLS.Stage4.HexClass
public import CFSG.GH74.GLS.Stage4.LocalGen
public import CFSG.GH74.GLS.Stage4.LocalSE

public section

namespace CFSG.GH74.GLS.Stage4

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.GH74.BNPair CFSG.GH74.GLS.SP CFSG.GH74.GLS.Stage4.Hex

@[expose] def Ch6Out (G : Type) [Group G] : Prop :=
  ∃ (p : ℕ) (H : Subgroup G) (r₁ r₂ : G) (U : Subgroup G) (root : ℤ → Subgroup G) (z : G)
    (S K₁ K₂ F P₀ : Subgroup G) (q : ℕ),
    Cor97 p H r₁ r₂ U root ∧ Gen97 p H r₁ r₂ U root z S K₁ K₂ F P₀ ∧ Odd q ∧
      ((5 ≤ q ∧ RootOrdersG2 root q) ∨ (3 ≤ q ∧ RootOrdersD4 root q))


section Orders

variable {X : Type*} [Group X]

@[expose] def HasSL2ProductOfIndexTwoCh6At (C₁ : Subgroup X) (q q₁ q₂ : ℕ) : Prop :=
  ∃ (F F₁ F₂ : Type) (_ : Field F) (_ : Field F₁) (_ : Field F₂) (_ : Finite F) (_ : Finite F₁)
    (_ : Finite F₂),
    Nat.card F = q ∧ Nat.card F₁ = q₁ ∧ Nat.card F₂ = q₂ ∧ Odd (Nat.card F₁) ∧
    Odd (Nat.card F₂) ∧ Nat.card F₂ ≤ Nat.card F₁ ∧ 5 ≤ Nat.card F₁ ∧
    (Nat.card ↥(StatedSL 2 F₁)).factorization 2 = (Nat.card ↥(StatedSL 2 F)).factorization 2 ∧
    (Nat.card ↥(StatedSL 2 F₂)).factorization 2 = (Nat.card ↥(StatedSL 2 F)).factorization 2 ∧
    ∃ K : Subgroup X, K ≤ C₁ ∧ (K.subgroupOf C₁).index = 2 ∧ IsCentralProductOfSL2 K F₁ F₂

theorem hasSL2ProductOfIndexTwoCh6_iff_exists_at (C₁ : Subgroup X) (q : ℕ) :
    HasSL2ProductOfIndexTwoCh6 C₁ q ↔ ∃ q₁ q₂ : ℕ, HasSL2ProductOfIndexTwoCh6At C₁ q q₁ q₂ := by
  constructor
  · rintro ⟨F, F₁, F₂, i, i₁, i₂, f, f₁, f₂, hq, ho₁, ho₂, hle, h5, hs₁, hs₂, K, hKC, hKi, hK⟩
    exact ⟨Nat.card F₁, Nat.card F₂, F, F₁, F₂, i, i₁, i₂, f, f₁, f₂, hq, rfl, rfl, ho₁, ho₂,
      hle, h5, hs₁, hs₂, K, hKC, hKi, hK⟩
  · rintro ⟨q₁, q₂, F, F₁, F₂, i, i₁, i₂, f, f₁, f₂, hq, -, -, ho₁, ho₂, hle, h5, hs₁, hs₂, K, hKC,
      hKi, hK⟩
    exact ⟨F, F₁, F₂, i, i₁, i₂, f, f₁, f₂, hq, ho₁, ho₂, hle, h5, hs₁, hs₂, K, hKC, hKi, hK⟩

end Orders

@[expose] def IsTwoCentralG2TypeG2At (G : Type) [Group G] (Gs : Type) [Group Gs]
    (q₁ q₂ : ℕ) : Prop :=
  (∃ (S : Sylow 2 G) (S' : Sylow 2 Gs), Nonempty (↥(S : Subgroup G) ≃* ↥(S' : Subgroup Gs))) ∧
    ∃ z : G, IsCentralInvolution z ∧ (∀ u : G, orderOf u = 2 → IsConj z u) ∧
      pPrimeCore 2 ↥(centralizer ({z} : Set G)) = ⊥ ∧
      ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ LieModel Gs .G2 0 p f ∧
        HasSL2ProductOfIndexTwoCh6At (oPrimeResidual 2 ↥(centralizer ({z} : Set G))) (p ^ f) q₁ q₂

theorem isTwoCentralG2TypeG2_iff_exists_at (G : Type) [Group G] (Gs : Type) [Group Gs] :
    IsTwoCentralG2TypeG2 G Gs ↔ ∃ q₁ q₂ : ℕ, IsTwoCentralG2TypeG2At G Gs q₁ q₂ := by
  constructor
  · rintro ⟨hS, z, hz, hconj, hO, p, f, hp, hp2, hL, hSL⟩
    obtain ⟨q₁, q₂, h⟩ := (hasSL2ProductOfIndexTwoCh6_iff_exists_at _ _).1 hSL
    exact ⟨q₁, q₂, hS, z, hz, hconj, hO, p, f, hp, hp2, hL, h⟩
  · rintro ⟨q₁, q₂, hS, z, hz, hconj, hO, p, f, hp, hp2, hL, h⟩
    exact ⟨hS, z, hz, hconj, hO, p, f, hp, hp2, hL,
      (hasSL2ProductOfIndexTwoCh6_iff_exists_at _ _).2 ⟨q₁, q₂, h⟩⟩


end CFSG.GH74.GLS.Stage4
