module

public import Certificates.Data.S1277Sig
public import CFSG.Quasithin.Vol2.Ch12Sec7GzSAct

public section

namespace CFSG.Quasithin.H13.I1277

open Certificates.Data.S1277Sig

theorem applyCols_nil (x : Nat) : applyCols [] x = 0 := rfl

theorem applyCols_cons (c : Nat) (cs : List Nat) (x : Nat) :
    applyCols (c :: cs) x = (if x % 2 = 1 then c else 0) ^^^ applyCols cs (x / 2) := rfl

theorem applyCols_zero (cols : List Nat) : applyCols cols 0 = 0 := by
  induction cols with
  | nil => rfl
  | cons c cs ih => rw [applyCols_cons]; simp [ih]

theorem applyCols_xor (cols : List Nat) : ∀ x y : Nat,
    applyCols cols (x ^^^ y) = applyCols cols x ^^^ applyCols cols y := by
  induction cols with
  | nil => intro x y; simp [applyCols_nil]
  | cons c cs ih =>
    intro x y
    rw [applyCols_cons, applyCols_cons, applyCols_cons, Nat.xor_div_two, ih]
    have hxy : (x ^^^ y) % 2 = (x + y) % 2 := Nat.xor_mod_two_eq
    rcases Nat.mod_two_eq_zero_or_one x with hx | hx <;>
      rcases Nat.mod_two_eq_zero_or_one y with hy | hy
    · have : (x ^^^ y) % 2 = 0 := by omega
      simp [hx, hy, this, Nat.xor_assoc, Nat.xor_comm, Nat.xor_left_comm]
    · have : (x ^^^ y) % 2 = 1 := by omega
      simp [hx, hy, this, Nat.xor_assoc, Nat.xor_comm, Nat.xor_left_comm]
    · have : (x ^^^ y) % 2 = 1 := by omega
      simp [hx, hy, this, Nat.xor_assoc, Nat.xor_comm, Nat.xor_left_comm]
    · have : (x ^^^ y) % 2 = 0 := by omega
      simp [hx, hy, this, Nat.xor_assoc, Nat.xor_comm, Nat.xor_left_comm]

theorem applyCols_lt {d : Nat} {cols : List Nat} (h : ∀ c ∈ cols, c < 2 ^ d) (x : Nat) :
    applyCols cols x < 2 ^ d := by
  induction cols generalizing x with
  | nil => rw [applyCols_nil]; exact Nat.two_pow_pos _
  | cons c cs ih =>
    rw [applyCols_cons]
    refine Nat.xor_lt_two_pow ?_ (ih (fun c' hc' => h c' (List.mem_cons_of_mem _ hc')) _)
    split_ifs
    · exact h c List.mem_cons_self
    · exact Nat.two_pow_pos _

theorem applyCols_append_lt (p q : List Nat) : ∀ x : Nat, x < 2 ^ p.length →
    applyCols (p ++ q) x = applyCols p x := by
  induction p with
  | nil =>
    intro x hx
    rw [List.length_nil, pow_zero] at hx
    have hx0 : x = 0 := by omega
    subst hx0
    simp [applyCols_zero]
  | cons c cs ih =>
    intro x hx
    simp only [List.cons_append, applyCols_cons]
    rw [ih (x / 2)]
    rw [List.length_cons, pow_succ] at hx
    omega

theorem applyCols_append_ge (c : Nat) (p : List Nat) : ∀ y : Nat, y < 2 ^ p.length →
    applyCols (p ++ [c]) (2 ^ p.length + y) = c ^^^ applyCols p y := by
  induction p with
  | nil =>
    intro y hy
    rw [List.length_nil, pow_zero] at hy
    have hy0 : y = 0 := by omega
    subst hy0
    simp [applyCols_cons, applyCols_nil]
  | cons c' cs ih =>
    intro y hy
    simp only [List.cons_append, applyCols_cons, List.length_cons]
    have hy' : y / 2 < 2 ^ cs.length := by
      rw [List.length_cons, pow_succ] at hy; omega
    have e1 : (2 ^ (cs.length + 1) + y) % 2 = y % 2 := by
      rw [pow_succ]; omega
    have e2 : (2 ^ (cs.length + 1) + y) / 2 = 2 ^ cs.length + y / 2 := by
      rw [pow_succ]; omega
    rw [e1, e2, ih (y / 2) hy']
    exact Nat.xor_left_comm _ _ _

theorem applyCols_pow (cols : List Nat) (i : Nat) (hi : i < cols.length) :
    applyCols cols (2 ^ i) = cols[i] := by
  induction cols generalizing i with
  | nil => simp at hi
  | cons c cs ih =>
    cases i with
    | zero => simp [applyCols_cons, applyCols_zero]
    | succ i =>
      rw [applyCols_cons]
      have e1 : 2 ^ (i + 1) % 2 = 0 := by rw [pow_succ]; omega
      have e2 : 2 ^ (i + 1) / 2 = 2 ^ i := by rw [pow_succ]; omega
      rw [e1, e2, ih i (by simpa using hi)]
      simp


theorem xor_pow_of_lt (k : Nat) : ∀ y, y < 2 ^ k → 2 ^ k ^^^ y = 2 ^ k + y := by
  induction k with
  | zero =>
    intro y hy
    rw [pow_zero] at hy
    have : y = 0 := by omega
    subst this; simp
  | succ k ih =>
    intro y hy
    have hy2 : y / 2 < 2 ^ k := by rw [pow_succ] at hy; omega
    have h1 : (2 ^ (k + 1) ^^^ y) % 2 = (2 ^ (k + 1) + y) % 2 := Nat.xor_mod_two_eq
    have h2 : (2 ^ (k + 1) ^^^ y) / 2 = (2 ^ (k + 1) + y) / 2 := by
      rw [Nat.xor_div_two, show 2 ^ (k + 1) / 2 = 2 ^ k by rw [pow_succ]; omega, ih _ hy2]
      rw [pow_succ]; omega
    omega

def colsOf {d : Nat} (σ : Equiv.Perm (Fin (2 ^ d))) : List Nat :=
  (List.range d).map fun i =>
    if h : i < d then (σ ⟨2 ^ i, Nat.pow_lt_pow_right (by norm_num) h⟩).1 else 0

theorem length_colsOf {d : Nat} (σ : Equiv.Perm (Fin (2 ^ d))) : (colsOf σ).length = d := by
  simp [colsOf]

theorem getElem_colsOf {d : Nat} (σ : Equiv.Perm (Fin (2 ^ d))) (i : Nat) (hi : i < d) :
    (colsOf σ)[i]'(by rw [length_colsOf]; exact hi) =
      (σ ⟨2 ^ i, Nat.pow_lt_pow_right (by norm_num) hi⟩).1 := by
  simp [colsOf, hi]

theorem applyCols_colsOf {d : Nat} {σ : Equiv.Perm (Fin (2 ^ d))}
    (hσ : ∀ a b c : Fin (2 ^ d), a.1 ^^^ b.1 = c.1 → (σ a).1 ^^^ (σ b).1 = (σ c).1) :
    ∀ x : Fin (2 ^ d), (σ x).1 = applyCols (colsOf σ) x.1 := by
  have h0 : (σ ⟨0, Nat.two_pow_pos d⟩).1 = 0 := by
    have := hσ ⟨0, Nat.two_pow_pos d⟩ ⟨0, Nat.two_pow_pos d⟩ ⟨0, Nat.two_pow_pos d⟩ (by simp)
    rw [Nat.xor_self] at this
    exact this.symm
  have key : ∀ k, k ≤ d → ∀ x (hx : x < 2 ^ d), x < 2 ^ k →
      (σ ⟨x, hx⟩).1 = applyCols ((colsOf σ).take k) x := by
    intro k
    induction k with
    | zero =>
      intro _ x hx hxk
      rw [pow_zero] at hxk
      have : x = 0 := by omega
      subst this
      simpa [applyCols_zero] using h0
    | succ k ih =>
      intro hk x hx hxk
      have hkd : k < d := hk
      have hlen : ((colsOf σ).take k).length = k := by
        rw [List.length_take, length_colsOf]; omega
      have htake : (colsOf σ).take (k + 1) = (colsOf σ).take k ++ [(colsOf σ)[k]'(by
          rw [length_colsOf]; exact hkd)] := List.take_succ_eq_append_getElem _
      rw [htake]
      by_cases hlt : x < 2 ^ k
      · rw [applyCols_append_lt _ _ x (by rw [hlen]; exact hlt)]
        exact ih (by omega) x hx hlt
      · obtain ⟨y, rfl⟩ : ∃ y, x = 2 ^ k + y := ⟨x - 2 ^ k, by omega⟩
        have hy : y < 2 ^ k := by rw [pow_succ] at hxk; omega
        have hyd : y < 2 ^ d := by
          have : 2 ^ k ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hkd.le
          omega
        have e1 := applyCols_append_ge ((colsOf σ)[k]'(by rw [length_colsOf]; exact hkd))
          ((colsOf σ).take k) y (by rw [hlen]; exact hy)
        rw [hlen] at e1
        have hσk := hσ ⟨2 ^ k, Nat.pow_lt_pow_right (by norm_num) hkd⟩ ⟨y, hyd⟩ ⟨2 ^ k + y, hx⟩
          (by simpa using xor_pow_of_lt k y hy)
        rw [← hσk, e1, ih (by omega) y hyd hy, getElem_colsOf σ k hkd]
  intro x
  have := key d le_rfl x.1 x.2 x.2
  rw [this, List.take_of_length_le (by rw [length_colsOf])]


theorem colsOf_injective {d : Nat} {φ : Nat → Nat} {σ τ : Equiv.Perm (Fin (2 ^ d))}
    (hσ : σ ∈ Sig d φ) (hτ : τ ∈ Sig d φ) (h : colsOf σ = colsOf τ) : σ = τ := by
  apply Equiv.ext
  intro x
  apply Fin.ext
  rw [applyCols_colsOf hσ.1 x, applyCols_colsOf hτ.1 x, h]


theorem colsOf_one (d : Nat) : colsOf (1 : Equiv.Perm (Fin (2 ^ d))) = idCols d := by
  apply List.ext_getElem
  · rw [length_colsOf]; simp [idCols]
  · intro i h1 h2
    have hi : i < d := by simpa [length_colsOf] using h1
    rw [getElem_colsOf _ i hi]
    simp [idCols]

theorem colsOf_mul {d : Nat} {σ : Equiv.Perm (Fin (2 ^ d))}
    (hσ : ∀ a b c : Fin (2 ^ d), a.1 ^^^ b.1 = c.1 → (σ a).1 ^^^ (σ b).1 = (σ c).1)
    (τ : Equiv.Perm (Fin (2 ^ d))) : colsOf (σ * τ) = compCols (colsOf σ) (colsOf τ) := by
  apply List.ext_getElem
  · rw [length_colsOf]; simp [compCols, length_colsOf]
  · intro i h1 h2
    have hi : i < d := by simpa [length_colsOf] using h1
    rw [getElem_colsOf _ i hi]
    simp only [compCols, List.getElem_map]
    rw [getElem_colsOf τ i hi]
    exact applyCols_colsOf hσ _

end CFSG.Quasithin.H13.I1277

end
