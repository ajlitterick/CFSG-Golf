module

public import Certificates.Data.CFSGNative.GL33.Check
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Data.Nat.Totient

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79.GL33

abbrev Vec := Fin 3 → ZMod 3

abbrev Mat := Matrix (Fin 3) (Fin 3) (ZMod 3)

@[expose] def decV (r : ℕ) : Vec :=
  ![((r % 3 : ℕ) : ZMod 3), (((r / 3) % 3 : ℕ) : ZMod 3), (((r / 9) % 3 : ℕ) : ZMod 3)]

@[expose] def encV (u : Vec) : ℕ := (u 0).val + 3 * (u 1).val + 9 * (u 2).val

@[expose] def dec (c : ℕ) : Mat :=
  Matrix.of ![decV (c % 27), decV ((c / 27) % 27), decV ((c / 729) % 27)]


theorem encV_lt (u : Vec) : encV u < 27 := by
  have h0 := ZMod.val_lt (u 0)
  have h1 := ZMod.val_lt (u 1)
  have h2 := ZMod.val_lt (u 2)
  unfold encV
  omega


theorem decV_encV (u : Vec) : decV (encV u) = u := by
  have h0 := ZMod.val_lt (u 0)
  have h1 := ZMod.val_lt (u 1)
  have h2 := ZMod.val_lt (u 2)
  have e0 : (encV u) % 3 = (u 0).val := by unfold encV; omega
  have e1 : (encV u) / 3 % 3 = (u 1).val := by unfold encV; omega
  have e2 : (encV u) / 9 % 3 = (u 2).val := by unfold encV; omega
  funext j
  fin_cases j <;> simp [decV, e0, e1, e2]

theorem encV_decV {r : ℕ} (hr : r < 27) : encV (decV r) = r := by
  unfold encV decV
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, ZMod.val_natCast]
  omega

theorem decV_inj {r r' : ℕ} (hr : r < 27) (hr' : r' < 27) (h : decV r = decV r') : r = r' := by
  rw [← encV_decV hr, ← encV_decV hr', h]


theorem decV_digits {d₀ d₁ d₂ : ℕ} (h₀ : d₀ < 3) (h₁ : d₁ < 3) (h₂ : d₂ < 3) :
    decV (d₀ + 3 * d₁ + 9 * d₂) = ![(d₀ : ZMod 3), (d₁ : ZMod 3), (d₂ : ZMod 3)] := by
  have e0 : (d₀ + 3 * d₁ + 9 * d₂) % 3 = d₀ := by omega
  have e1 : (d₀ + 3 * d₁ + 9 * d₂) / 3 % 3 = d₁ := by omega
  have e2 : (d₀ + 3 * d₁ + 9 * d₂) / 9 % 3 = d₂ := by omega
  unfold decV
  rw [e0, e1, e2]


theorem det3 (a0 a1 a2 b0 b1 b2 c0 c1 c2 : ℕ) :
    (Matrix.of ![![(a0 : ZMod 3), a1, a2], ![b0, b1, b2], ![c0, c1, c2]] : Mat).det =
      ((a0 * b1 * c2 + a1 * b2 * c0 + a2 * b0 * c1 +
        2 * (a0 * b2 * c1 + a1 * b0 * c2 + a2 * b1 * c0) : ℕ) : ZMod 3) := by
  rw [Matrix.det_fin_three]
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  push_cast
  have h2 : (2 : ZMod 3) = -1 := by decide
  rw [h2]
  simp only [sub_eq_add_neg]
  ring1

theorem det_dec (c : ℕ) : (dec c).det =
    ((((c % 27) % 3) * ((((c / 27) % 27) / 3) % 3) * ((((c / 729) % 27) / 9) % 3) +
      (((c % 27) / 3) % 3) * ((((c / 27) % 27) / 9) % 3) * (((c / 729) % 27) % 3) +
      (((c % 27) / 9) % 3) * (((c / 27) % 27) % 3) * ((((c / 729) % 27) / 3) % 3) +
    2 * ((((c % 27) % 3) * ((((c / 27) % 27) / 9) % 3) * ((((c / 729) % 27) / 3) % 3) +
      (((c % 27) / 3) % 3) * (((c / 27) % 27) % 3) * ((((c / 729) % 27) / 9) % 3) +
      (((c % 27) / 9) % 3) * ((((c / 27) % 27) / 3) % 3) * (((c / 729) % 27) % 3))) : ℕ) :
      ZMod 3) := by
  rw [← det3]
  rfl


end CFSG.RankThree.PartTwo.Sec21.FF79.GL33

end
