module

public import Certificates.Data.G2ThreeMaxCheck

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87.G2ThreeCert

open Certificates.G2ThreeMax

abbrev Mat3 : Type := Matrix (Fin 14) (Fin 14) (ZMod 3)

@[expose] def M (a : Array ℕ) : Mat3 := Matrix.of fun r c => ((a[14 * r.val + c.val]! : ℕ) : ZMod 3)

theorem ofFn_get (f : Fin 196 → ℕ) {p : ℕ} (hp : p < 196) : (Array.ofFn f)[p]! = f ⟨p, hp⟩ := by
  rw [getElem!_pos _ p (by simpa using hp)]
  exact Array.getElem_ofFn _

theorem idx_lt (r c : Fin 14) : 14 * r.val + c.val < 196 := by
  have := r.2; have := c.2; omega


theorem M_idArr : M idArr = 1 := by
  ext r c
  simp only [M, idArr, Matrix.of_apply, Matrix.one_apply]
  rw [ofFn_get _ (idx_lt r c)]
  have h1 : (14 * r.val + c.val) / 14 = r.val := by have := c.2; omega
  have h2 : (14 * r.val + c.val) % 14 = c.val := by have := c.2; omega
  simp only [h1, h2, Fin.val_inj]
  split_ifs <;> simp_all

theorem M_mmul (a b : Array ℕ) : M (mmul a b) = M a * M b := by
  ext r c
  simp only [M, mmul, Matrix.of_apply, Matrix.mul_apply]
  rw [ofFn_get _ (idx_lt r c)]
  have h1 : (14 * r.val + c.val) / 14 = r.val := by have := c.2; omega
  have h2 : (14 * r.val + c.val) % 14 = c.val := by have := c.2; omega
  simp only [h1, h2]
  rw [ZMod.natCast_mod, Nat.cast_sum, Finset.sum_range]
  simp [Nat.cast_mul]


end CFSG.GH74.GLS.Stage2.Signalizer.Odd87.G2ThreeCert
