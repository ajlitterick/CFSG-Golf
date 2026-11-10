module

public import CFSG.Foundations.Basic
public import CFSG.GroupTheory.QuaternionCentralizers

public section

namespace CFSG.ComponentClassification.SmallLocal

open Subgroup QuaternionGroup

variable {X : Type*} [Group X]

theorem mul_pow_rearrange {z x y : X} (hzx : Commute z x) (hzy : Commute z y)
    (hxy : Commute x y) (A B C A' B' C' : ℕ) :
    z ^ A * x ^ B * y ^ C * (z ^ A' * x ^ B' * y ^ C') =
      z ^ A * z ^ A' * (x ^ B * x ^ B') * (y ^ C * y ^ C') := by
  have h1 : Commute (y ^ C) (z ^ A') := (hzy.pow_pow A' C).symm
  have h2 : Commute (x ^ B) (z ^ A') := (hzx.pow_pow A' B).symm
  have h3 : Commute (y ^ C) (x ^ B') := (hxy.pow_pow B' C).symm
  calc z ^ A * x ^ B * y ^ C * (z ^ A' * x ^ B' * y ^ C')
      = z ^ A * (x ^ B * (y ^ C * z ^ A')) * x ^ B' * y ^ C' := by simp only [mul_assoc]
    _ = z ^ A * (x ^ B * (z ^ A' * y ^ C)) * x ^ B' * y ^ C' := by rw [h1.eq]
    _ = z ^ A * ((x ^ B * z ^ A') * y ^ C) * x ^ B' * y ^ C' := by simp only [mul_assoc]
    _ = z ^ A * ((z ^ A' * x ^ B) * y ^ C) * x ^ B' * y ^ C' := by rw [h2.eq]
    _ = z ^ A * z ^ A' * (x ^ B * (y ^ C * x ^ B')) * y ^ C' := by simp only [mul_assoc]
    _ = z ^ A * z ^ A' * (x ^ B * (x ^ B' * y ^ C)) * y ^ C' := by rw [h3.eq]
    _ = z ^ A * z ^ A' * (x ^ B * x ^ B') * (y ^ C * y ^ C') := by simp only [mul_assoc]

theorem exists_elementaryAbelian_eight {z x y : X} (hz : z ^ 2 = 1) (hx : x ^ 2 = 1)
    (hy : y ^ 2 = 1) (hzx : Commute z x) (hzy : Commute z y) (hxy : Commute x y)
    (hind : ∀ a b c : ℕ, a < 2 → b < 2 → c < 2 → z ^ a * x ^ b * y ^ c = 1 →
      a = 0 ∧ b = 0 ∧ c = 0) :
    ∃ E : Subgroup X, IsElementaryAbelian 2 E ∧ Nat.card E = 8 ∧ z ∈ E ∧
      E ≤ closure {z, x, y} := by
  have hmod : ∀ w : X, w ^ 2 = 1 → ∀ m : ℕ, w ^ (m % 2) = w ^ m := fun w hw m =>
    (pow_eq_pow_mod m hw).symm
  let f : Multiplicative (ZMod 2 × ZMod 2 × ZMod 2) → X := fun v =>
    z ^ (Multiplicative.toAdd v).1.val * x ^ (Multiplicative.toAdd v).2.1.val *
      y ^ (Multiplicative.toAdd v).2.2.val
  have hf : ∀ v w, f (v * w) = f v * f w := by
    intro v w
    simp only [f, toAdd_mul, Prod.fst_add, Prod.snd_add, ZMod.val_add, hmod z hz, hmod x hx,
      hmod y hy, pow_add]
    exact (mul_pow_rearrange hzx hzy hxy _ _ _ _ _ _).symm
  let ψ : Multiplicative (ZMod 2 × ZMod 2 × ZMod 2) →* X :=
    { toFun := f
      map_one' := by simp [f]
      map_mul' := hf }
  have hψ : ∀ v, ψ v = f v := fun v => rfl
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro v hv
    rw [hψ] at hv
    obtain ⟨ha, hb, hc⟩ := hind _ _ _ (ZMod.val_lt _) (ZMod.val_lt _) (ZMod.val_lt _) hv
    rw [ZMod.val_eq_zero] at ha hb hc
    exact toAdd_eq_zero.mp (Prod.ext ha (Prod.ext hb hc))
  have hsq : ∀ v : Multiplicative (ZMod 2 × ZMod 2 × ZMod 2), v ^ 2 = 1 := by decide
  refine ⟨ψ.range, ?_, ?_, ⟨Multiplicative.ofAdd (1, 0, 0), ?_⟩, ?_⟩
  · refine { toIsMulCommutative := ⟨⟨fun a b => ?_⟩⟩, exponent_dvd_p := ?_ }
    · obtain ⟨_, v, rfl⟩ := a
      obtain ⟨_, w, rfl⟩ := b
      apply Subtype.ext
      change ψ v * ψ w = ψ w * ψ v
      rw [← map_mul, ← map_mul, mul_comm]
    · refine Monoid.exponent_dvd_of_forall_pow_eq_one fun a => ?_
      obtain ⟨_, v, rfl⟩ := a
      apply Subtype.ext
      change ψ v ^ 2 = 1
      rw [← map_pow, hsq, map_one]
  · rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv,
      Nat.card_congr Multiplicative.toAdd, Nat.card_prod, Nat.card_prod, Nat.card_zmod]
  · rw [hψ]
    simp only [f, toAdd_ofAdd, show (1 : ZMod 2).val = 1 from rfl,
      show (0 : ZMod 2).val = 0 from rfl, pow_one, pow_zero, mul_one]
  · rintro _ ⟨v, rfl⟩
    rw [hψ]
    exact mul_mem (mul_mem (pow_mem (subset_closure (by simp)) _)
      (pow_mem (subset_closure (by simp)) _)) (pow_mem (subset_closure (by simp)) _)


end CFSG.ComponentClassification.SmallLocal
