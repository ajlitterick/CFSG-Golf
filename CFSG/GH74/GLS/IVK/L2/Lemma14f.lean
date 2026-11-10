module

public import CFSG.GH74.GLS.IVK.L2.Fixed14a
public import CFSG.GH74.GLS.IVK.L2.FieldProj

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup CFSG CFSG.GorensteinWalter

theorem le_of_pow_dvd_mul_sq_sub_one {p m j : ℕ} (hp : p.Prime) (hm : 1 ≤ m)
    (h : p ^ j ∣ p ^ m * ((p ^ m) ^ 2 - 1)) : j ≤ m := by
  have hcop : Nat.Coprime (p ^ j) ((p ^ m) ^ 2 - 1) := by
    apply Nat.Coprime.pow_left
    rw [hp.coprime_iff_not_dvd]
    intro hdvd
    have h1 : p ∣ (p ^ m) ^ 2 := dvd_pow (dvd_pow_self p (by omega)) (by norm_num)
    have h2 : p ∣ (p ^ m) ^ 2 - ((p ^ m) ^ 2 - 1) := Nat.dvd_sub h1 hdvd
    have h3 : (p ^ m) ^ 2 - ((p ^ m) ^ 2 - 1) = 1 := by
      have : 1 ≤ (p ^ m) ^ 2 := Nat.one_le_pow 2 (p ^ m) (pow_pos hp.pos m)
      omega
    rw [h3] at h2
    exact hp.one_lt.ne' (Nat.dvd_one.mp h2)
  have := hcop.dvd_of_dvd_mul_right h
  exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp this


section Unipotent


end Unipotent

section Rank

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] [Finite K] (e : K ≃* L2 F)
  (σ : F ≃+* F)

include e σ in
theorem card_le_of_pow_eq_one {p m : ℕ} (hp : p.Prime) (hq₀ : Nat.card (fixedField σ) = p ^ m)
    (hm : 1 ≤ m) (A : Subgroup (MulAut K))
    (hAC : A ≤ centralizer ({fieldAutHom e σ} : Set (MulAut K)))
    (hpow : ∀ x ∈ A, x ^ p = 1) : Nat.card A ≤ p ^ (m + 1) := by
  have : Fact p.Prime := ⟨hp⟩
  set ψ : ↥A →* (F ≃+* F) := (fieldProj e).comp A.subtype with hψ
  have hpowA : ∀ a : ↥A, a ^ p = 1 := fun a => Subtype.ext (by simpa using hpow a a.2)
  have hrange : Nat.card ψ.range ≤ p := by
    have := ringAut_isCyclic F
    have : IsCyclic ψ.range := Subgroup.isCyclic _
    have h1 : Monoid.exponent ψ.range ∣ p := by
      rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
      rintro ⟨_, a, rfl⟩
      apply Subtype.ext
      show ψ a ^ p = 1
      rw [← map_pow, hpowA a, map_one]
    rw [IsCyclic.exponent_eq_card] at h1
    exact Nat.le_of_dvd hp.pos h1
  have hker : Nat.card ψ.ker ≤ p ^ m := by
    set X : Subgroup (MulAut K) := ψ.ker.map A.subtype with hX
    have hXA : X ≤ A := by
      rintro _ ⟨a, _, rfl⟩
      exact a.2
    have hXle : X ≤ centralizer ({fieldAutHom e σ} : Set (MulAut K)) ⊓ innDiagSub e := by
      intro x hx
      obtain ⟨a, ha, rfl⟩ := hx
      exact ⟨hAC a.2, (mem_innDiagSub_iff e _).mpr (MonoidHom.mem_ker.mp ha)⟩
    have hXcard : Nat.card X = Nat.card ψ.ker :=
      Subgroup.card_map_of_injective A.subtype_injective
    have hdvd : Nat.card X ∣ p ^ m * ((p ^ m) ^ 2 - 1) := by
      have h1 := Subgroup.card_dvd_of_le hXle
      rw [card_centralizer_fieldAut e σ, hq₀] at h1
      exact h1
    have hXp : IsPGroup p X := by
      intro x
      refine ⟨1, ?_⟩
      apply Subtype.ext
      simpa using hpow x (hXA x.2)
    obtain ⟨j, hj⟩ := (IsPGroup.iff_card).mp hXp
    rw [hj] at hdvd
    have := le_of_pow_dvd_mul_sq_sub_one hp hm hdvd
    rw [← hXcard, hj]
    exact Nat.pow_le_pow_right hp.pos this
  have := Subgroup.card_ker_mul_card_range ψ
  calc Nat.card A = Nat.card ψ.ker * Nat.card ψ.range := this.symm
    _ ≤ p ^ m * p := Nat.mul_le_mul hker hrange
    _ = p ^ (m + 1) := by ring

end Rank


end CFSG.GH74.GLS.IVK
