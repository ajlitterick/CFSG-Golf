module

public import Certificates.Data.Kernel.LocalQT.Lat
import Mathlib.Tactic.IntervalCases
import Mathlib.Data.List.GetD
public import Mathlib.Data.Nat.Notation

public section

namespace CFSG.KC.LQT.L

theorem andB_eq (a b : Bool) : CFSG.KC.Ord.andB a b = (a && b) := by
  cases a <;> rfl

theorem allA_eq_true {α : Type} (l : List α) (f : α → Bool) :
    allA l f = true ↔ ∀ x ∈ l, f x = true := by
  induction l with
  | nil => exact ⟨fun _ _ h => absurd h List.not_mem_nil, fun _ => rfl⟩
  | cons x l ih =>
    have e : allA (x :: l) f = CFSG.KC.Ord.andB (f x) (allA l f) := rfl
    rw [e, andB_eq, Bool.and_eq_true, ih, List.forall_mem_cons]

theorem allA_cons {α : Type} {x : α} {l : List α} {f : α → Bool} (h₁ : f x = true)
    (h₂ : allA l f = true) : allA (x :: l) f = true := by
  have e : allA (x :: l) f = CFSG.KC.Ord.andB (f x) (allA l f) := rfl
  rw [e, h₁, h₂]
  rfl

theorem allA_of_getD {α : Type} (l : List α) (f : α → Bool) (x₀ : α)
    (h : ∀ i < l.length, f (l.getD i x₀) = true) : allA l f = true := by
  refine (allA_eq_true l f).2 fun x hx => ?_
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  have := h i hi
  rwa [List.getD_eq_getElem _ _ hi] at this


end CFSG.KC.LQT.L

end
