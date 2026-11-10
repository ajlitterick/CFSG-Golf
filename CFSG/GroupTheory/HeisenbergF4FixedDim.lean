module

public import CFSG.Fischer.F4
public import Std.Tactic.BVDecide.Normalize.Prop

public section

open scoped commutatorElement

open CFSG.Fischer

namespace CFSG.GroupTheory.HeisenbergF4

@[ext]
structure H27 where
  a : ZMod 3
  b : ZMod 3
  c : ZMod 3
deriving DecidableEq, Fintype

namespace H27

@[expose] def mul (x y : H27) : H27 :=
  ⟨x.a + y.a, x.b + y.b, x.c + y.c + x.a * y.b⟩

@[expose] def inv (x : H27) : H27 :=
  ⟨-x.a, -x.b, -x.c + x.a * x.b⟩

instance : Mul H27 := ⟨mul⟩
instance : Inv H27 := ⟨inv⟩
instance : One H27 := ⟨⟨0, 0, 0⟩⟩

@[simp] theorem mul_a (x y : H27) : (x * y).a = x.a + y.a := rfl
@[simp] theorem mul_b (x y : H27) : (x * y).b = x.b + y.b := rfl
@[simp] theorem mul_c (x y : H27) : (x * y).c = x.c + y.c + x.a * y.b := rfl

@[simp] theorem inv_a (x : H27) : x⁻¹.a = -x.a := rfl
@[simp] theorem inv_b (x : H27) : x⁻¹.b = -x.b := rfl
@[simp] theorem inv_c (x : H27) : x⁻¹.c = -x.c + x.a * x.b := rfl

@[simp] theorem one_a : (1 : H27).a = 0 := rfl
@[simp] theorem one_b : (1 : H27).b = 0 := rfl
@[simp] theorem one_c : (1 : H27).c = 0 := rfl

@[expose] def c0 : H27 := ⟨0, 0, 1⟩

@[simp] theorem c0_a : c0.a = 0 := rfl
@[simp] theorem c0_b : c0.b = 0 := rfl
@[simp] theorem c0_c : c0.c = 1 := rfl

instance : Group H27 :=
  Group.ofLeftAxioms
    (fun x y z => by
      ext <;> simp only [mul_a, mul_b, mul_c] <;> ring)
    (fun x => by
      ext <;> simp only [mul_a, mul_b, mul_c, one_a, one_b, one_c] <;> ring)
    (fun x => by
      ext
      · change (x⁻¹ * x).a = (1 : H27).a
        rw [mul_a, inv_a, one_a]
        abel
      · change (x⁻¹ * x).b = (1 : H27).b
        rw [mul_b, inv_b, one_b]
        abel
      · change (x⁻¹ * x).c = (1 : H27).c
        rw [mul_c, inv_c, inv_a, one_c]
        have h : (-x.a) * x.b = -(x.a * x.b) := neg_mul x.a x.b
        rw [h]
        abel)

def toProd : H27 ≃ ZMod 3 × ZMod 3 × ZMod 3 where
  toFun x := (x.a, x.b, x.c)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv x := by cases x; rfl
  right_inv p := by rcases p with ⟨a, b, c⟩; rfl

theorem card : Fintype.card H27 = 27 := by
  rw [Fintype.card_congr toProd]
  decide

theorem exponent_three : ∀ x : H27, x ^ 3 = 1 := by decide

theorem noncommutative : ∃ x y : H27, x * y ≠ y * x := by
  refine ⟨⟨1, 0, 0⟩, ⟨0, 1, 0⟩, ?_⟩
  decide

def centerSubgroup : Subgroup H27 where
  carrier := {x | x.a = 0 ∧ x.b = 0}
  one_mem' := by simp
  mul_mem' := by
    rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    simp [hx1, hx2, hy1, hy2]
  inv_mem' := by
    rintro x ⟨hx1, hx2⟩
    constructor <;> (simp [hx1, hx2]; exact neg_zero)

theorem mem_centerSubgroup_iff (x : H27) :
    x ∈ centerSubgroup ↔ x.a = 0 ∧ x.b = 0 := Iff.rfl

theorem center_eq : Subgroup.center H27 = centerSubgroup := by
  ext x
  rw [Subgroup.mem_center_iff, mem_centerSubgroup_iff]
  constructor
  · intro h
    have h1 : x.c = x.c + x.a := by
      simpa [mul_a, mul_b, mul_c] using congrArg H27.c (h ⟨0, 1, 0⟩)
    have h2 : x.c + x.b = x.c := by
      simpa [mul_a, mul_b, mul_c] using congrArg H27.c (h ⟨1, 0, 0⟩)
    constructor
    · linear_combination -h1
    · linear_combination h2
  · rintro ⟨hx1, hx2⟩ g
    ext <;> simp [mul_a, mul_b, mul_c, hx1, hx2, add_comm]

theorem commutator_mem_center (x y : H27) : ⁅x, y⁆ ∈ centerSubgroup := by
  rw [mem_centerSubgroup_iff]
  constructor
  · rw [commutatorElement_def]
    simp only [mul_a, mul_b, mul_c, inv_a, inv_b, inv_c]
    abel
  · rw [commutatorElement_def]
    simp only [mul_a, mul_b, mul_c, inv_a, inv_b, inv_c]
    abel


def centerEquiv : centerSubgroup ≃ ZMod 3 where
  toFun x := x.1.c
  invFun z := ⟨⟨0, 0, z⟩, by simp [centerSubgroup]⟩
  left_inv x := by
    rcases x with ⟨⟨a, b, c⟩, hx⟩
    rw [mem_centerSubgroup_iff] at hx
    change a = 0 ∧ b = 0 at hx
    ext <;> simp [hx.1, hx.2]
  right_inv z := rfl

theorem card_center : Nat.card centerSubgroup = 3 := by
  rw [Nat.card_congr centerEquiv, Nat.card_eq_fintype_card, ZMod.card]


theorem nat_card : Nat.card H27 = 27 := by
  rw [Nat.card_eq_fintype_card, card]

end H27


variable {W : Type*} [AddCommGroup W] [Module F4 W] [FiniteDimensional F4 W]


section F2

local instance : Algebra (ZMod 2) F4 := ZMod.algebra F4 2
local instance : Module (ZMod 2) W := Module.compHom W (algebraMap (ZMod 2) F4)
local instance : IsScalarTower (ZMod 2) F4 W where
  smul_assoc r s w := by
    change (algebraMap (ZMod 2) F4 r * s) • w = algebraMap (ZMod 2) F4 r • (s • w)
    rw [mul_smul]

theorem finrank_f2_eq_two : Module.finrank (ZMod 2) F4 = 2 := by
  have hcard : 2 ^ Module.finrank (ZMod 2) F4 = 4 := by
    simpa [F4.card] using FiniteField.pow_finrank_eq_card 2 F4
  have hcard' : 2 ^ Module.finrank (ZMod 2) F4 = 2 ^ 2 := by
    simpa using hcard
  exact Nat.pow_right_injective (by norm_num) hcard'


end F2

end CFSG.GroupTheory.HeisenbergF4
