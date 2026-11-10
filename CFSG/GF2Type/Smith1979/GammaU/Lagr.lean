module

public import CFSG.GF2Type.Smith1979.GammaU.SpanList
public import CFSG.GF2Type.Smith1979.GammaU.Group

public section

namespace CFSG.GF2Type.Smith1979.GammaU

open Module

@[expose] def f0b (m n : ℕ) : Bool :=
  (List.range 6).foldl
    (fun acc i => acc ^^ ((m.testBit i && n.testBit (6 + i)) ^^ (m.testBit (6 + i) && n.testBit i)))
    false

theorem prod_term (p q r s : Bool) :
    ((if p then 1 else 0 : ZMod 2) * (if q then 1 else 0) +
        (if r then 1 else 0) * if s then 1 else 0) =
      if ((p && q) ^^ (r && s)) then 1 else 0 := by
  cases p <;> cases q <;> cases r <;> cases s <;> decide

theorem f0_vecOf (m n : ℕ) : f0 (vecOf m) (vecOf n) = if f0b m n then 1 else 0 := by
  simp only [f0, vecOf, Fin.sum_univ_six, f0b, List.range_succ, List.range_zero, List.nil_append,
    List.foldl_append, List.foldl_cons, List.foldl_nil, Bool.false_xor, prod_term, ite_add_ite]
  rfl

theorem f0_eq_zero_of_mem {D : Submodule (ZMod 2) V12} (hsing : ∀ x ∈ D, q0 x = 0) {x y : V12}
    (hx : x ∈ D) (hy : y ∈ D) : f0 x y = 0 := by
  rw [← polar_q0, QuadraticMap.polar, hsing _ (D.add_mem hx hy), hsing x hx, hsing y hy, sub_zero,
    sub_zero]

theorem eq_false_of_ite {b : Bool} (h : (if b then 1 else 0 : ZMod 2) = 0) : b = false := by
  cases b
  · rfl
  · exact absurd h (by decide)


section Complete


end Complete

end CFSG.GF2Type.Smith1979.GammaU
