module

public import CFSG.Quasithin.Background.B4Models
public import CFSG.Quasithin.Background.E3Defs

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin.E3

section H9

variable {W : Type} [CommGroup W]

@[expose] def stabV (U : Subgroup W) : Subgroup (MulAut W) where
  carrier := {g | ∀ u : W, u ∈ U ↔ g u ∈ U}
  one_mem' := fun _ => Iff.rfl
  mul_mem' := fun {a b} ha hb u => (hb u).trans (ha (b u))
  inv_mem' := fun {a} ha u => by
    have h := ha (a⁻¹ u)
    rw [show a (a⁻¹ u) = u from MulAut.apply_inv_self _ _ _] at h
    exact h.symm

@[expose] def IsDualH9 (L : Subgroup (MulAut W)) (W₁ W₂ : Subgroup W) (β : W → W → ZMod 2) :
    Prop :=
  (∀ a ∈ W₁, ∀ b ∈ W₁, ∀ c ∈ W₂, β (a * b) c = β a c + β b c) ∧
    (∀ a ∈ W₁, ∀ c ∈ W₂, ∀ d ∈ W₂, β a (c * d) = β a c + β a d) ∧
    (∀ a ∈ W₁, a ≠ 1 → ∃ c ∈ W₂, β a c = 1) ∧ (∀ c ∈ W₂, c ≠ 1 → ∃ a ∈ W₁, β a c = 1) ∧
    ∀ l ∈ L, ∀ a ∈ W₁, ∀ c ∈ W₂, β (l a) (l c) = β a c


@[expose] def IsTransvOn (g : MulAut W) (W₁ : Subgroup W) : Prop :=
  g ∈ stabV W₁ ∧ (fixV (Subgroup.zpowers g) ⊓ W₁).relIndex W₁ = 2

@[expose] def conjAut (A : Subgroup (MulAut W)) (m : MulAut W) : Subgroup (MulAut W) :=
  A.map (MulAut.conj m).toMonoidHom

structure H9Hyp (n : ℕ) (M L T : Subgroup (MulAut W)) (W₁ W₂ : Subgroup W) : Prop where
  rank : n = 4 ∨ n = 5
  exp : ∀ w : W, w ^ 2 = 1
  aut : Nonempty (↥M ≃* MulAut (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)))
  le : L ≤ M
  index : L.relIndex M = 2
  sylow_le : T ≤ M
  sylow_two : IsPGroup 2 ↥T
  sylow_odd : ¬ 2 ∣ T.relIndex M
  inf : W₁ ⊓ W₂ = ⊥
  sup : W₁ ⊔ W₂ = ⊤
  inv₁ : L ≤ stabV W₁
  inv₂ : L ≤ stabV W₂
  card₁ : Nat.card W₁ = 2 ^ n
  full : ∀ φ : MulAut ↥W₁, ∃ l ∈ L, ∀ w : ↥W₁, l w = φ w
  faith : ∀ l ∈ L, (∀ w ∈ W₁, l w = w) → l = 1
  swap : ∃ t ∈ T, t ∉ L ∧ W₂ = W₁.map t.toMonoidHom


end H9


@[expose] def LemH9Comm : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (n : ℕ) (M L T : Subgroup (MulAut W))
    (W₁ W₂ : Subgroup W), H9Hyp n M L T W₁ W₂ → ∀ X : Subgroup (MulAut W), X ≤ M →
      IsElemAbelian2 X → Nat.card (commV X) ≤ 2 ^ 2 → Nat.card X ≤ 2

@[expose] def LemH9Cent : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (n : ℕ) (M L T : Subgroup (MulAut W))
    (W₁ W₂ : Subgroup W), H9Hyp n M L T W₁ W₂ → ∀ X : Subgroup (MulAut W), X ≤ M →
      IsElemAbelian2 X → Nat.card W ≤ 2 ^ 2 * Nat.card (fixV X) → Nat.card X ≤ 2

@[expose] def LemH9Axes : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (n : ℕ) (M L T : Subgroup (MulAut W))
    (W₁ W₂ : Subgroup W), H9Hyp n M L T W₁ W₂ → ∀ B : Subgroup (MulAut W), B ≤ L →
      IsElemAbelian2 B → 2 ^ (n - 2) ≤ Nat.card B →
      (∀ b ∈ B, ∀ c ∈ B, b ≠ 1 → c ≠ 1 →
        fixV (Subgroup.zpowers b) ⊓ W₁ = fixV (Subgroup.zpowers c) ⊓ W₁ ∧
          fixV (Subgroup.zpowers b) ⊓ W₂ = fixV (Subgroup.zpowers c) ⊓ W₂) →
      n = 4 ∧ Nat.card B = 2 ^ 2 ∧
        ∀ b ∈ B, b ≠ 1 → Nat.card ↥(fixV (Subgroup.zpowers b) ⊓ W₁) = 2 ^ 2

@[expose] def LemH9FF5 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (M L T : Subgroup (MulAut W)) (W₁ W₂ : Subgroup W),
    H9Hyp 5 M L T W₁ W₂ → ∀ A : Subgroup (MulAut W), A ≤ M → IsElemAbelian2 A → A ≠ ⊥ →
      Nat.card A ≤ 2 ^ 4 → Nat.card W ≤ Nat.card A * Nat.card (fixV A) →
      Nat.card (Subgroup.closure {x : W | ∃ a ∈ A, ∃ w ∈ W₁, x = a w * w⁻¹}) ≤ 2 ^ 2 ∧
        2 ^ 2 ≤ (fixV A ⊓ W₁).relIndex W₁

@[expose] def LemH9Rank4 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (M L T : Subgroup (MulAut W)) (W₁ W₂ : Subgroup W),
    H9Hyp 4 M L T W₁ W₂ → ∀ A : Subgroup (MulAut W), A ≤ M → IsElemAbelian2 A →
      Nat.card A ≤ 2 ^ 4

@[expose] def LemH9FF4 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (M L T : Subgroup (MulAut W)) (W₁ W₂ : Subgroup W),
    H9Hyp 4 M L T W₁ W₂ → ∀ A : Subgroup (MulAut W), A ≤ M → IsElemAbelian2 A → A ≠ ⊥ →
      Nat.card W ≤ Nat.card A * Nat.card (fixV A) → A ≤ L

@[expose] def LemH93Use : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (M L T : Subgroup (MulAut W)) (W₁ W₂ : Subgroup W),
    H9Hyp 4 M L T W₁ W₂ → ∃ A₀ A₁ A₂ : Subgroup (MulAut W),
      (∀ A ∈ ({A₀, A₁, A₂} : Set (Subgroup (MulAut W))),
        A ≤ M ∧ IsElemAbelian2 A ∧ Nat.card A = 2 ^ 4) ∧
      (∀ A : Subgroup (MulAut W), A ≤ M → IsElemAbelian2 A → Nat.card A = 2 ^ 4 →
        ∃ m ∈ M, A = conjAut A₀ m ∨ A = conjAut A₁ m ∨ A = conjAut A₂ m) ∧
      (Nat.card (fixV A₀) = 2 ^ 4 ∧ gammaCheck 2 A₀ = ⊤) ∧
      (Nat.card (fixV A₁) = 2 ∧ Nat.card (gammaCheck 2 A₁) = 2 ^ 6) ∧
      (Nat.card (fixV A₂) = 2 ^ 2 ∧ Nat.card (gammaCheck 2 A₂) = 2 ^ 6 ∧
        ∀ a ∈ A₂, (∀ w ∈ gammaCheck 2 A₂, a w = w) → a = 1) ∧
      ∀ A ∈ ({A₁, A₂} : Set (Subgroup (MulAut W))),
        (∃ b ∈ A ⊓ L, IsTransvOn b W₁) ∧ (∃ b ∈ A ⊓ L, b ≠ 1 ∧ ¬ IsTransvOn b W₁) ∧
          2 ^ 7 ≤ Nat.card (gammaCheck 3 A)

@[expose] def LemH92Use : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (M L T : Subgroup (MulAut W)) (W₁ W₂ : Subgroup W)
    (β : W → W → ZMod 2), H9Hyp 5 M L T W₁ W₂ → IsDualH9 L W₁ W₂ β →
    ∀ A : Subgroup (MulAut W), A ≤ M → IsElemAbelian2 A → 2 ^ 5 ≤ Nat.card A →
      A ≤ L ∧ gammaCheck 3 A = ⊤ ∧
        (Nat.card ↥(fixV A ⊓ W₁) ≤ 2 ^ 2 ∨ Nat.card ↥(fixV A ⊓ W₂) ≤ 2 ^ 2)

end CFSG.Quasithin.H13
