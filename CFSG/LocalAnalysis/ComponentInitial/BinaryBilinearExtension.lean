module

public import CFSG.LocalAnalysis.ComponentInitial.BinaryQuadraticRefinement
public import Mathlib.FieldTheory.Finiteness

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open scoped commutatorElement

variable {U W : Type*} [AddCommGroup U] [Module (ZMod 2) U] [AddCommGroup W] [Module (ZMod 2) W]

@[ext] structure BinExt (b : U →ₗ[ZMod 2] U →ₗ[ZMod 2] W) where
  fst : U
  snd : W

namespace BinExt

variable {b : U →ₗ[ZMod 2] U →ₗ[ZMod 2] W}

@[expose] def op (x y : BinExt b) : BinExt b :=
  ⟨x.fst + y.fst, x.snd + y.snd + b x.fst y.fst⟩

variable (b) in
@[expose] def zero : BinExt b := ⟨0, 0⟩

variable (b) in
@[expose] def iota (w : W) : BinExt b := ⟨0, w⟩

@[expose] def pi (x : BinExt b) : U := x.fst

variable (b) in
@[expose] def center0 : Set (BinExt b) := {x | x.fst = 0}

theorem add_self_zmod {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] (x : V) : x + x = 0 :=
  two_smul_eq_zero_of_zmod x

instance : Group (BinExt b) where
  mul := op
  mul_assoc x y z := by
    ext
    · exact add_assoc _ _ _
    · change x.snd + y.snd + b x.fst y.fst + z.snd + b (x.fst + y.fst) z.fst =
        x.snd + (y.snd + z.snd + b y.fst z.fst) + b x.fst (y.fst + z.fst)
      simp only [map_add, LinearMap.add_apply]
      abel
  one := zero b
  one_mul x := by
    ext
    · exact zero_add _
    · change 0 + x.snd + b 0 x.fst = x.snd
      simp
  mul_one x := by
    ext
    · exact add_zero _
    · change x.snd + 0 + b x.fst 0 = x.snd
      simp
  inv x := ⟨x.fst, x.snd + b x.fst x.fst⟩
  inv_mul_cancel x := by
    ext
    · exact add_self_zmod x.fst
    · change x.snd + b x.fst x.fst + x.snd + b x.fst x.fst = 0
      rw [show x.snd + b x.fst x.fst + x.snd + b x.fst x.fst =
        (x.snd + x.snd) + (b x.fst x.fst + b x.fst x.fst) by abel, add_self_zmod, add_self_zmod,
        add_zero]

theorem mul_def (x y : BinExt b) : x * y = ⟨x.fst + y.fst, x.snd + y.snd + b x.fst y.fst⟩ := rfl

theorem one_def : (1 : BinExt b) = ⟨0, 0⟩ := rfl

theorem inv_def (x : BinExt b) : x⁻¹ = ⟨x.fst, x.snd + b x.fst x.fst⟩ := rfl

theorem sq_def (x : BinExt b) : x ^ 2 = ⟨0, b x.fst x.fst⟩ := by
  rw [sq, mul_def]
  ext
  · exact add_self_zmod _
  · change x.snd + x.snd + b x.fst x.fst = b x.fst x.fst
    rw [add_self_zmod, zero_add]

theorem commutator_def (x y : BinExt b) :
    x⁻¹ * y⁻¹ * x * y = ⟨0, b x.fst y.fst + b y.fst x.fst⟩ := by
  simp only [mul_def, inv_def]
  ext
  · change x.fst + y.fst + x.fst + y.fst = 0
    rw [show x.fst + y.fst + x.fst + y.fst = (x.fst + x.fst) + (y.fst + y.fst) by abel,
      add_self_zmod, add_self_zmod, add_zero]
  · change x.snd + b x.fst x.fst + (y.snd + b y.fst y.fst) + b x.fst y.fst + x.snd +
      b (x.fst + y.fst) x.fst + y.snd + b (x.fst + y.fst + x.fst) y.fst =
        b x.fst y.fst + b y.fst x.fst
    simp only [map_add, LinearMap.add_apply]
    have h1 := add_self_zmod x.snd
    have h2 := add_self_zmod y.snd
    have h3 := add_self_zmod (b x.fst x.fst)
    have h4 := add_self_zmod (b y.fst y.fst)
    have h5 := add_self_zmod (b x.fst y.fst)
    rw [← sub_eq_zero]
    have e : x.snd + b x.fst x.fst + (y.snd + b y.fst y.fst) + b x.fst y.fst + x.snd +
        (b x.fst x.fst + b y.fst x.fst) + y.snd + (b x.fst y.fst + b y.fst y.fst +
          b x.fst y.fst) - (b x.fst y.fst + b y.fst x.fst) =
        (x.snd + x.snd) + (y.snd + y.snd) + (b x.fst x.fst + b x.fst x.fst) +
          (b y.fst y.fst + b y.fst y.fst) + (b x.fst y.fst + b x.fst y.fst) := by abel
    rw [e, h1, h2, h3, h4, h5]
    simp

variable (b) in
@[expose] def iotaHom : Multiplicative W →* BinExt b where
  toFun w := iota b w.toAdd
  map_one' := rfl
  map_mul' w z := by
    ext
    · exact (add_zero 0).symm
    · change w.toAdd + z.toAdd = w.toAdd + z.toAdd + b 0 0
      simp

variable (b) in
@[expose] def piHom : BinExt b →* Multiplicative U where
  toFun x := Multiplicative.ofAdd x.fst
  map_one' := rfl
  map_mul' _ _ := rfl

variable (b) in
@[expose] def centerSub : Subgroup (BinExt b) := (piHom b).ker

instance : (centerSub b).Normal := (piHom b).normal_ker


end BinExt

open BinExt


end CFSG.LocalAnalysis.ComponentInitial
