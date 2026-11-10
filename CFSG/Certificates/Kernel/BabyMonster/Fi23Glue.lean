module

public import CFSG.Sporadic.GLQ.RegisterProgram

public section

namespace CFSG.KC.BM.Fi23Glue

open CFSG.Sporadic.GLQ

variable {G : Type*} [Group G]

@[expose] def invWord (w : List ℤ) : List ℤ := (w.map Neg.neg).reverse

theorem letter_neg (x y : G) (l : ℤ) (hl : l = 1 ∨ l = 2) : letter x y (-l) = (letter x y l)⁻¹ := by
  rcases hl with rfl | rfl <;> simp [letter]

theorem signedWord_append (x y : G) (u v : List ℤ) :
    signedWord x y (u ++ v) = signedWord x y u * signedWord x y v := by
  simp [signedWord]

theorem signedWord_invWord (x y : G) (p : List ℤ) (hp : ∀ l ∈ p, l = 1 ∨ l = 2) :
    signedWord x y (invWord p) = (signedWord x y p)⁻¹ := by
  induction p with
  | nil => simp [invWord, signedWord]
  | cons l p ih =>
    have hl := hp l List.mem_cons_self
    have ih := ih fun l' h => hp l' (List.mem_cons_of_mem _ h)
    have e : invWord (l :: p) = invWord p ++ [-l] := by simp [invWord]
    rw [e, signedWord_append, ih]
    simp [signedWord, letter_neg x y l hl, mul_inv_rev]

theorem signedWord_conj (x y : G) (p m : List ℤ) (hp : ∀ l ∈ p, l = 1 ∨ l = 2) :
    signedWord x y (p ++ m ++ invWord p) =
      signedWord x y p * signedWord x y m * (signedWord x y p)⁻¹ := by
  rw [signedWord_append, signedWord_append, signedWord_invWord x y p hp]


theorem conj_sq {p d : G} (h : d * d = 1) : (p * d * p⁻¹) * (p * d * p⁻¹) = 1 := by
  simp [mul_assoc, ← mul_assoc d, h]

theorem comm_relator {X Y : G} (hX : X * X = 1) (hY : Y * Y = 1) (h : X * Y = Y * X) :
    X * Y * (X * Y) = 1 := by
  rw [mul_assoc, ← mul_assoc Y, ← h, mul_assoc, hY, mul_one, hX]


end CFSG.KC.BM.Fi23Glue

end
