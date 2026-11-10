module

public import CFSG.RankThree.PartOne.KC.MatrixAlgebraCenter
public import CFSG.RankThree.PartOne.KC.MatrixAlgebraFieldProduct
public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.RankThree.PartOne

namespace KCMatrixAlgebra

theorem mul_inv_mem_of_pow_two_pow_mem {G : Type*} [CommGroup G] [Finite G] (σ : MulAut G)
    (hσ : ∀ (x : G) (k : ℕ), x ^ 2 ^ k = 1 → σ x = x) (C : Subgroup G)
    (hC : ∀ x ∈ C, σ x ∈ C) {g : G} {k : ℕ} (hg : g ^ 2 ^ k ∈ C) : σ g * g⁻¹ ∈ C := by
  obtain ⟨e, b, hb, hn⟩ := Nat.exists_eq_two_pow_mul_odd (n := Nat.card G) Nat.card_pos.ne'
  have hgb : σ (g ^ b) = g ^ b := by
    apply hσ _ e
    rw [← pow_mul, mul_comm, ← hn, pow_card_eq_one']
  rw [map_pow] at hgb
  have hy1 : (σ g * g⁻¹) ^ b = 1 := by
    rw [mul_pow, inv_pow, hgb, mul_inv_cancel]
  have hy2 : (σ g * g⁻¹) ^ 2 ^ k ∈ C := by
    rw [mul_pow, inv_pow, ← map_pow]
    exact C.mul_mem (hC _ hg) (C.inv_mem hg)
  have hcop : IsCoprime ((2 ^ k : ℕ) : ℤ) (b : ℤ) :=
    Nat.isCoprime_iff_coprime.2 (Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hb))
  obtain ⟨u, v, huv⟩ := hcop
  have huv' : ((2 ^ k : ℕ) : ℤ) * u + (b : ℤ) * v = 1 := by linarith
  have : σ g * g⁻¹ = ((σ g * g⁻¹) ^ 2 ^ k) ^ u := by
    calc σ g * g⁻¹ = (σ g * g⁻¹) ^ (((2 ^ k : ℕ) : ℤ) * u + (b : ℤ) * v) := by
          rw [huv', zpow_one]
      _ = ((σ g * g⁻¹) ^ 2 ^ k) ^ u := by
        rw [zpow_add, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast, hy1, one_zpow, mul_one]
  rw [this]
  exact C.zpow_mem hy2 u

variable {p : ℕ} {r : ℕ} {K : Fin r → Type*} [∀ i, Field (K i)] {m : Fin r → ℕ}
  {R : Type*} [Ring R] {A : Type*} [Group A]

theorem centerUnitsAut_apply_eq_of_pow_two_pow_eq_one (hp : p.Prime) (hp2 : p ≠ 2) (hrp : r < p)
    (hm : ∀ i, 0 < m i) (e : R ≃+* ∀ i, Matrix (Fin (m i)) (Fin (m i)) (K i))
    (hA : IsPGroup p A) (φ : A →* RingAut R) (a : A) {x : (Subring.center R)ˣ} {k : ℕ}
    (hx : x ^ 2 ^ k = 1) : centerUnitsAut (φ a) x = x := by
  let ζ : (∀ i, K i) ≃+* Subring.center R :=
    (scalarCenterEquiv K m hm).trans (Subring.centerCongr e.symm)
  let ψ : A →* RingAut (∀ i, K i) :=
    { toFun := fun b => ζ.trans ((centerRingAut (φ b)).trans ζ.symm)
      map_one' := by
        ext c
        simp
      map_mul' := fun b c => by
        ext d
        simp }
  have hc : (ζ.symm (x : Subring.center R)) ^ 2 ^ k = 1 := by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, hx, Units.val_one, map_one]
  have h := ringAut_apply_eq_of_pow_two_pow_eq_one hp hp2
    (ι := Fin r) (by simpa using hrp) hA ψ a hc
  have h2 := congrArg ζ h
  have h3 := congrArg Subtype.val (by simpa [ψ] using h2 :
    centerRingAut (φ a) (x : Subring.center R) = (x : Subring.center R))
  exact Units.ext (Subtype.ext (by simpa using h3))


end KCMatrixAlgebra


end CFSG.RankThree.PartOne
