module

public import CFSG.ClassicalInvolution.RouteD.PatternBasic

public section

namespace CFSG.ClassicalInvolution.RouteD

open TauCeti

variable {n : ℕ}


@[expose] def picA (n : ℕ) (t : ℕ → ZMod 2) : Fin n → ZMod 2 := fun j => t j + t (j + 1)


@[expose] def prefixSum (v : Fin n → ZMod 2) : ℕ → ZMod 2
  | 0 => 0
  | k + 1 => prefixSum v k + (if h : k < n then v ⟨k, h⟩ else 0)

theorem picA_prefixSum (v : Fin n → ZMod 2) : picA n (prefixSum v) = v := by
  funext j
  have key : ∀ x y : ZMod 2, x + (x + y) = y := by decide
  simp only [picA, prefixSum, j.isLt, dite_true]
  exact key _ _


end CFSG.ClassicalInvolution.RouteD
