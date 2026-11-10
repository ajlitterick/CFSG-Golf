
module

public import CFSG.Monster.B.TwoA.Sp8.GenActionHomBase
public import CFSG.Monster.B.TwoA.Sp8.QuadCosetBase

@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Sp8

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.B CFSG.Monster.B.TwoA

@[expose] def qv (v : V8) : QuadraticForm (ZMod 2) V8 :=
  qForm + QuadraticMap.linMulLin (b0 v) (b0 v)

theorem qv_apply (v w : V8) : qv v w = qPoly w + b0 v w := by
  change qForm w + QuadraticMap.linMulLin (b0 v) (b0 v) w = _
  rw [QuadraticMap.linMulLin_apply, qForm_apply, zmod2_mul_self]

theorem b0_comm (v w : V8) : b0 v w = b0 w v := by
  rw [← polarBilin_qForm, QuadraticMap.polarBilin_apply_apply,
    QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm]

theorem qv_apply' (v w : V8) : qv v w = qPoly (w + v) + qPoly v := by
  rw [qv_apply, b0_comm, b0_eq_qPoly]
  ring_nf
  simp only [sub_eq_add_neg, ZModModule.neg_eq_self]

theorem polarBilin_qv (v : V8) : QuadraticMap.polarBilin (qv v) = b0 := by
  refine LinearMap.ext fun x => LinearMap.ext fun y => ?_
  rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, qv_apply, qv_apply, qv_apply,
    map_add, b0_eq_qPoly x y]
  ring

theorem qv_zero : qv 0 = qForm := by
  ext w
  rw [qv_apply, map_zero, LinearMap.zero_apply, add_zero, qForm_apply]

theorem qv_injective : Function.Injective qv := by
  intro v w h
  have h1 : ∀ u, b0 v u = b0 w u := fun u => by
    have := congrArg (fun Q : QuadraticForm (ZMod 2) V8 => Q u) h
    simp only [qv_apply] at this
    exact add_left_cancel this
  have h2 : ∀ u, b0 (v - w) u = 0 := fun u => by rw [map_sub, LinearMap.sub_apply, h1, sub_self]
  exact sub_eq_zero.1 (nondegenerate_b0.1 _ h2)


end CFSG.Monster.B.TwoA.Sp8
