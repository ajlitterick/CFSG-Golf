module

public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.PairAlt
public import CFSG.Certificates.CosetTablePresented
public import Mathlib.GroupTheory.FreeGroup.Reduce

public section

namespace CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation

open CFSG.CosetTable

structure CDesc (k : ℕ) where
  letter : Fin k × Bool
  conj : FreeGroup (Fin k)
  deriving DecidableEq

variable {k : ℕ}

@[expose] def CDesc.elt (c : CDesc k) : FreeGroup (Fin k) :=
  c.conj⁻¹ * FreeGroup.mk [c.letter] * c.conj

@[expose] def evalW {J : Type*} [Group J] (x : Fin k → J) (w : FreeGroup (Fin k)) : J :=
  FreeGroup.lift x w

theorem evalW_mul {J : Type*} [Group J] (x : Fin k → J) (a b : FreeGroup (Fin k)) :
    evalW x (a * b) = evalW x a * evalW x b := map_mul _ _ _

theorem evalW_inv {J : Type*} [Group J] (x : Fin k → J) (a : FreeGroup (Fin k)) :
    evalW x a⁻¹ = (evalW x a)⁻¹ := map_inv _ _

theorem evalW_pow {J : Type*} [Group J] (x : Fin k → J) (a : FreeGroup (Fin k)) (n : ℕ) :
    evalW x (a ^ n) = (evalW x a) ^ n := map_pow _ _ _

theorem evalW_of {J : Type*} [Group J] (x : Fin k → J) (i : Fin k) :
    evalW x (FreeGroup.of i) = x i := by simp [evalW]

theorem evalW_one {J : Type*} [Group J] (x : Fin k → J) : evalW x 1 = 1 := map_one _

theorem evalW_cdesc_elt {J : Type*} [Group J] (x : Fin k → J) (c : CDesc k) :
    evalW x c.elt =
      (evalW x c.conj)⁻¹ * evalW x (FreeGroup.mk [c.letter]) * evalW x c.conj := by
  simp only [CDesc.elt, evalW_mul, evalW_inv]

theorem evalW_letter {J : Type*} [Group J] (x : Fin k → J) (l : Fin k × Bool) :
    evalW x (FreeGroup.mk [l]) = if l.2 then x l.1 else (x l.1)⁻¹ := by
  obtain ⟨i, b⟩ := l
  cases b <;> simp [evalW]

@[expose] def alt (p q : FreeGroup (Fin k)) : Fin 6 → List (FreeGroup (Fin k))
  | 0 => [p * q]
  | 1 => [p * q⁻¹]
  | 2 => [p * q * p⁻¹ * q⁻¹]
  | 3 => [(p * q) ^ 2]
  | 4 => [(p * q⁻¹) ^ 2]
  | 5 => [(p * q) ^ 5, (p * q * p * q⁻¹) ^ 2, (p * q⁻¹) ^ 5, (p * q⁻¹ * p * q) ^ 2]

inductive Tree (k : ℕ) where
  | collapse : ℕ → Tree k
  | success : CDesc k → Tree k
  | branch : CDesc k → CDesc k → Tree k → Tree k → Tree k → Tree k → Tree k → Tree k → Tree k

@[expose] def Tree.succs : Tree k → List (CDesc k)
  | .collapse _ => []
  | .success t => [t]
  | .branch _ _ t0 t1 t2 t3 t4 t5 =>
      t0.succs ++ t1.succs ++ t2.succs ++ t3.succs ++ t4.succs ++ t5.succs


theorem exists_alt_eval {J : Type*} [Group J] (x : Fin k → J) (c1 c2 : CDesc k)
    (hpa : PairAlt (evalW x c1.elt) (evalW x c2.elt)) :
    ∃ i : Fin 6, ∀ r ∈ alt c1.elt c2.elt i, evalW x r = 1 := by
  set p := c1.elt
  set q := c2.elt
  rcases hpa with h | h | h | h | h | ⟨h1, h2, h3, h4⟩
  · refine ⟨0, ?_⟩
    intro r hr
    simp only [alt, List.mem_singleton] at hr
    subst hr
    rw [evalW_mul]; exact h
  · refine ⟨1, ?_⟩
    intro r hr
    simp only [alt, List.mem_singleton] at hr
    subst hr
    rw [evalW_mul, evalW_inv]; exact h
  · refine ⟨2, ?_⟩
    intro r hr
    simp only [alt, List.mem_singleton] at hr
    subst hr
    simp only [evalW_mul, evalW_inv]
    rw [h]
    group
  · refine ⟨3, ?_⟩
    intro r hr
    simp only [alt, List.mem_singleton] at hr
    subst hr
    rw [evalW_pow, evalW_mul]; exact h
  · refine ⟨4, ?_⟩
    intro r hr
    simp only [alt, List.mem_singleton] at hr
    subst hr
    rw [evalW_pow, evalW_mul, evalW_inv]; exact h
  · refine ⟨5, ?_⟩
    intro r hr
    simp only [alt, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [evalW_pow, evalW_mul]; exact h1
    · simp only [evalW_pow, evalW_mul, evalW_inv]; exact h2
    · rw [evalW_pow, evalW_mul, evalW_inv]; exact h3
    · simp only [evalW_pow, evalW_mul, evalW_inv]; exact h4


end CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation

end
