module

public import CFSG.CharacterTheory.Wreathed.AdaptedBaseFusionSupport
public import CFSG.CharacterTheory.Wreathed.BrauerWongBaseFusion
public import CFSG.CharacterTheory.Wreathed.BrauerWongMaximalOrder
public import CFSG.CharacterTheory.Wreathed.BrauerWongSylowCentralizer

public noncomputable section

namespace CFSG.Wreathed.OrderThirtyTwo

open CFSG.Wreathed CFSG.Wreathed.BrauerWong CFSG.Wreathed.AdaptedBaseFusion
open CFSG.Wreathed.WreathCentralSquare

universe u

variable {G : Type u} [Group G]

theorem orderOf_eq_of_isConj {a b : G} (h : IsConj a b) : orderOf a = orderOf b := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  rw [← hc, show c * a * c⁻¹ = (MulAut.conj c) a by simp, MulEquiv.orderOf_eq]

variable (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ 2))

theorem root_eq : wreathModelHom S e (originalRoot (2 ^ 2)) =
    wreathModelHom S e (Original.s (2 ^ 2)) * wreathModelHom S e (Original.z (2 ^ 2)) := by
  rw [originalRoot, map_mul]

theorem root_eq_element : wreathModelHom S e (Original.s (2 ^ 2)) *
    wreathModelHom S e (Original.z (2 ^ 2)) = wreathModelHom S e (element (2 ^ 2) 1 0 1) := by
  rw [← root_eq, originalRoot_eq]


theorem orderOf_element_swap {c d : ZMod (2 ^ 2)} (hcd : Odd (c + d).val) :
    orderOf (wreathModelHom S e (element (2 ^ 2) c d 1)) = 2 * 2 ^ 2 := by
  rw [orderOf_injective _ (wreathModelHom_injective S e)]
  exact (element_maximal_order_iff 1 c d 1).mpr ⟨rfl, hcd⟩

theorem orderOf_root : orderOf (wreathModelHom S e (Original.s (2 ^ 2)) *
    wreathModelHom S e (Original.z (2 ^ 2))) = 2 * 2 ^ 2 := by
  rw [root_eq_element]
  exact orderOf_element_swap S e (by decide)


variable [Finite G]


omit [Finite G] in
include e in
theorem card_sylow : Nat.card (S : Subgroup G) = 32 := by
  rw [Nat.card_congr e.toEquiv, (wreath_center_involution_and_quaternion_coordinates 2
    (le_refl 2)).card]
  rfl


end CFSG.Wreathed.OrderThirtyTwo
