module

public import Certificates.Data.CFSGNative.MonsterB.P0Rank
public import Mathlib.Data.Nat.Bitwise

public section

namespace CFSG.Monster.B.TwoA.Sp8.P0Rank

open MonsterB.P0Rank

private theorem xor_mod_two (a b : ℕ) :
    (a ^^^ b) % 2 = (a % 2) ^^^ (b % 2) := by
  have h := Nat.xor_mod_two_pow (a := a) (b := b) (n := 1)
  simpa using h

private theorem xor_mul_two (a b : ℕ) :
    (a ^^^ b) * 2 = a * 2 ^^^ b * 2 := by
  have h : (a ^^^ b) <<< 1 = a <<< 1 ^^^ b <<< 1 := Nat.shiftLeft_xor_distrib
  simpa [Nat.shiftLeft_eq] using h

private theorem two_mul_xor (a b : ℕ) :
    2 * (a ^^^ b) = 2 * a ^^^ 2 * b := by
  rw [Nat.mul_comm 2 (a ^^^ b), Nat.mul_comm 2 a, Nat.mul_comm 2 b]
  exact xor_mul_two a b

private theorem two_mul_div_two_xor_mod_two (x : ℕ) :
    2 * (x / 2) ^^^ (x % 2) = x := by
  have h : 2 ^ 1 * (x / 2) ^^^ (x % 2) = 2 ^ 1 * (x / 2) + x % 2 := by
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Nat.testBit_xor, Nat.testBit_two_pow_mul_add (x / 2) (by omega) j]
    by_cases hji : j < 1
    · rw [if_pos hji]
      have hz : (2 ^ 1 * (x / 2)).testBit j = false := by
        rw [Nat.testBit_two_pow_mul]
        simp [Nat.not_le.mpr hji]
      rw [hz, Bool.false_xor]
    · rw [if_neg hji]
      have hge : 1 ≤ j := Nat.le_of_not_lt hji
      have h1 : (2 ^ 1 * (x / 2)).testBit j = (x / 2).testBit (j - 1) := by
        rw [Nat.testBit_two_pow_mul]
        simp [hge]
      have hlt : (x % 2).testBit j = false := by
        apply Nat.testBit_lt_two_pow
        calc x % 2 < 2 ^ 1 := by omega
          _ ≤ 2 ^ j := Nat.pow_le_pow_right (by decide) hge
      rw [h1, hlt, Bool.xor_false]
  have hx : 2 ^ 1 * (x / 2) + x % 2 = x := by
    simpa [Nat.pow_one] using Nat.div_add_mod x 2
  rwa [hx] at h

theorem colsAct_zero (cs : List ℕ) : colsAct cs 0 = 0 := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [colsAct, ih]

theorem colsAct_xor (cs : List ℕ) (a b : ℕ) :
    colsAct cs (a ^^^ b) = colsAct cs a ^^^ colsAct cs b := by
  induction cs generalizing a b with
  | nil => simp [colsAct]
  | cons c cs ih =>
    have hc : (if a % 2 ^^^ b % 2 = 1 then c else 0) =
        (if a % 2 = 1 then c else 0) ^^^ (if b % 2 = 1 then c else 0) := by
      rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;>
        rcases Nat.mod_two_eq_zero_or_one b with hb | hb <;> simp [ha, hb]
    rw [colsAct.eq_2, xor_mod_two, Nat.xor_div_two, ih, colsAct.eq_2, colsAct.eq_2, hc]
    ac_rfl

theorem colsAct_lt {cs : List ℕ} {w : ℕ} (h : ∀ c ∈ cs, c < 2 ^ w) (x : ℕ) :
    colsAct cs x < 2 ^ w := by
  induction cs generalizing x with
  | nil => simpa [colsAct] using Nat.two_pow_pos w
  | cons c cs ih =>
    rw [colsAct.eq_2]
    refine Nat.xor_lt_two_pow ?_ ?_
    · split_ifs
      · exact h c (by simp)
      · exact Nat.two_pow_pos w
    · exact ih (fun c' hc' => h c' (by simp [hc'])) (x / 2)

theorem colsAct_colsOf {n : ℕ} {f : ℕ → ℕ} (hf : ∀ a b, f (a ^^^ b) = f a ^^^ f b) {x : ℕ}
    (hx : x < 2 ^ n) : colsAct (colsOf n f) x = f x := by
  have hf0 : f 0 = 0 := by
    have h := hf 0 0
    rw [Nat.zero_xor, Nat.xor_self] at h
    exact h
  induction n generalizing f x with
  | zero =>
    have hx0 : x = 0 := by simpa using hx
    subst hx0
    simp [colsOf, colsAct, hf0]
  | succ n ih =>
    have hcols : colsOf (n + 1) f = f 1 :: colsOf n (fun y => f (2 * y)) := by
      simp [colsOf, List.range_succ_eq_map, Nat.pow_succ, Nat.mul_comm]
    have hbit : (if x % 2 = 1 then f 1 else 0) = f (x % 2) := by
      rcases Nat.mod_two_eq_zero_or_one x with h | h <;> simp [h, hf0]
    have hlin : ∀ a b, (fun y => f (2 * y)) (a ^^^ b) =
        (fun y => f (2 * y)) a ^^^ (fun y => f (2 * y)) b := by
      intro a b
      show f (2 * (a ^^^ b)) = f (2 * a) ^^^ f (2 * b)
      rw [two_mul_xor, hf]
    have hx' : x / 2 < 2 ^ n := by
      rw [Nat.pow_succ] at hx
      have h2 : 0 < 2 ^ n := Nat.two_pow_pos n
      omega
    rw [hcols, colsAct.eq_2, hbit, ih (f := fun y => f (2 * y)) hlin hx' hf0,
      ← hf (x % 2) (2 * (x / 2)),
      Nat.xor_comm (x % 2) (2 * (x / 2)), two_mul_div_two_xor_mod_two]


private theorem foldr_actK_zero (cols : List (List ℕ)) (κ : ℕ) :
    ∀ l : List ℕ,
      l.foldr (fun k y => if κ.testBit k then colsAct (cols.getD k []) y else y) 0 = 0 := by
  intro l
  induction l with
  | nil => rfl
  | cons k l ih =>
    rw [List.foldr_cons, ih]
    split_ifs with hk
    · exact colsAct_zero _
    · rfl

theorem actK_zero (cols : List (List ℕ)) (κ : ℕ) : actK cols κ 0 = 0 := by
  rw [actK.eq_1]
  exact foldr_actK_zero cols κ (List.range cols.length)

private theorem foldr_actK_xor (cols : List (List ℕ)) (κ : ℕ) :
    ∀ l : List ℕ, ∀ a b : ℕ,
      l.foldr (fun k y => if κ.testBit k then colsAct (cols.getD k []) y else y) (a ^^^ b) =
        l.foldr (fun k y => if κ.testBit k then colsAct (cols.getD k []) y else y) a ^^^
          l.foldr (fun k y => if κ.testBit k then colsAct (cols.getD k []) y else y) b := by
  intro l
  induction l with
  | nil => intro a b; simp
  | cons k l ih =>
    intro a b
    rw [List.foldr_cons, List.foldr_cons, List.foldr_cons, ih]
    split_ifs with hk
    · exact colsAct_xor _ _ _
    · rfl

theorem actK_xor (cols : List (List ℕ)) (κ a b : ℕ) :
    actK cols κ (a ^^^ b) = actK cols κ a ^^^ actK cols κ b := by
  rw [actK.eq_1, actK.eq_1, actK.eq_1]
  exact foldr_actK_xor cols κ (List.range cols.length) a b

private theorem foldr_actK_zero_left (cols : List (List ℕ)) (x : ℕ) :
    ∀ l : List ℕ,
      l.foldr (fun k y => if (0 : ℕ).testBit k then colsAct (cols.getD k []) y else y) x = x := by
  intro l
  induction l with
  | nil => rfl
  | cons k l ih =>
    rw [List.foldr_cons, ih, Nat.zero_testBit]
    simp

theorem actK_zero_left (cols : List (List ℕ)) (x : ℕ) : actK cols 0 x = x := by
  rw [actK.eq_1]
  exact foldr_actK_zero_left cols x (List.range cols.length)

private theorem foldr_actK_lt (cols : List (List ℕ)) (κ : ℕ) {w : ℕ}
    (h : ∀ cs ∈ cols, ∀ c ∈ cs, c < 2 ^ w) (x : ℕ) (hx : x < 2 ^ w) :
    ∀ l : List ℕ, (∀ k ∈ l, k < cols.length) →
      l.foldr (fun k y => if κ.testBit k then colsAct (cols.getD k []) y else y) x < 2 ^ w := by
  intro l
  induction l with
  | nil => intro _; simpa using hx
  | cons k l ih =>
    intro hl
    rw [List.foldr_cons]
    split_ifs with hb
    · apply colsAct_lt
      intro c hc
      refine h (cols.getD k []) ?_ c hc
      rw [List.getD_eq_getElem cols [] (hl k (by simp))]
      exact List.getElem_mem (hl k (by simp))
    · exact ih (fun k' hk' => hl k' (by simp [hk']))

theorem actK_lt {cols : List (List ℕ)} {w : ℕ} (h : ∀ cs ∈ cols, ∀ c ∈ cs, c < 2 ^ w) (κ : ℕ)
    {x : ℕ} (hx : x < 2 ^ w) : actK cols κ x < 2 ^ w := by
  rw [actK.eq_1]
  exact foldr_actK_lt cols κ h x hx (List.range cols.length) (fun k hk => by simpa using hk)


end CFSG.Monster.B.TwoA.Sp8.P0Rank
