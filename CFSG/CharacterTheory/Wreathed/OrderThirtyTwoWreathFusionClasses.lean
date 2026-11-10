module

public import CFSG.CharacterTheory.Wreathed.OrderThirtyTwoWreathFusionCoordinates
public import CFSG.CharacterTheory.Wreathed.AdaptedBaseFusionAction

public noncomputable section

namespace CFSG.Wreathed.OrderThirtyTwo

open CFSG.Wreathed CFSG.Wreathed.BrauerWong CFSG.Wreathed.AdaptedBaseFusion

universe u

@[expose] def orbitRel (p q : ZMod 4 × ZMod 4) : Prop :=
  q = p ∨ q = cycleMap p ∨ q = cycleMap (cycleMap p) ∨ q = swapMap p ∨
    q = swapMap (cycleMap p) ∨ q = swapMap (cycleMap (cycleMap p))

instance (p q : ZMod 4 × ZMod 4) : Decidable (orbitRel p q) := by
  unfold orbitRel
  infer_instance


theorem swapMap_eq : ∀ p : ZMod 4 × ZMod 4,
    p.1.val • ((0, 1) : ZMod 4 × ZMod 4) + p.2.val • ((1, 0) : ZMod 4 × ZMod 4) = swapMap p := by
  decide


variable {G : Type u} [Group G]

theorem conj_pow_eq (k x : G) (n : ℕ) : k⁻¹ * x ^ n * k = (k⁻¹ * x * k) ^ n := by
  have h := conj_pow (a := k⁻¹) (b := x) (i := n)
  rw [inv_inv] at h
  exact h.symm

theorem conj_mul_eq (k x y : G) : k⁻¹ * (x * y) * k = (k⁻¹ * x * k) * (k⁻¹ * y * k) := by
  group

variable [Finite G] {S : Sylow 2 G} {e : S ≃* Wreath (2 ^ 2)} {σ υ g : G}
  (h : IsAdaptedBase (modelBase S e) (wreathModelHom S e (Original.a (2 ^ 2)))
    (wreathModelHom S e (Original.z (2 ^ 2))) σ υ g)
include h

theorem orderOf_left_eq : orderOf σ = 4 := orderOf_left h

theorem orderOf_right_eq : orderOf υ = 4 := orderOf_right h

theorem left_pow_four : σ ^ 4 = 1 := by
  rw [← orderOf_left_eq h]
  exact pow_orderOf_eq_one σ

theorem right_pow_four : υ ^ 4 = 1 := by
  rw [← orderOf_right_eq h]
  exact pow_orderOf_eq_one υ

omit [Finite G] in
theorem commute_left_right' : Commute σ υ :=
  modelBase_commute S e _ _ h.left_mem h.right_mem

theorem coord_inj {p q : ZMod 4 × ZMod 4} (hpq : coord σ υ p = coord σ υ q) : p = q :=
  coord_injective (left_pow_four h) (right_pow_four h) (commute_left_right' h)
    (orderOf_left_eq h) (orderOf_right_eq h) (zpowers_left_inf_right h) hpq

theorem exists_coord_of_mem {u : G} (hu : u ∈ modelBase S e) :
    ∃ p : ZMod 4 × ZMod 4, u = coord σ υ p := by
  rw [← h.closure_eq] at hu
  exact exists_coord (left_pow_four h) (right_pow_four h) (commute_left_right' h) hu


theorem swap_coord (p : ZMod 4 × ZMod 4) :
    (wreathModelHom S e (Original.z (2 ^ 2)))⁻¹ * coord σ υ p *
      wreathModelHom S e (Original.z (2 ^ 2)) = coord σ υ (swapMap p) := by
  set W := wreathModelHom S e (Original.z (2 ^ 2))
  have hW : W⁻¹ = W := swap_inv S e
  have hσW : W⁻¹ * σ * W = υ := h.conj_swap
  have hυW : W⁻¹ * υ * W = σ := by
    rw [← hσW, hW]
    calc W * (W * σ * W) * W = (W * W) * σ * (W * W) := by simp only [mul_assoc]
      _ = σ := by rw [show W * W = 1 by rw [← mul_inv_cancel W, hW], one_mul, mul_one]
  have hc := commute_left_right' h
  rw [coord, conj_mul_eq, conj_pow_eq, conj_pow_eq, hσW, hυW, ← swapMap_eq,
    ← coord_mul (left_pow_four h) (right_pow_four h) hc,
    ← coord_pow (left_pow_four h) (right_pow_four h) hc,
    ← coord_pow (left_pow_four h) (right_pow_four h) hc, coord_left, coord_right]


end CFSG.Wreathed.OrderThirtyTwo
