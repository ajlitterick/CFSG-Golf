module

public import CFSG.Walter.Ree.Thompson2.BaseRel.Iso
public import CFSG.Walter.Ree.Thompson3.Base

public section

namespace CFSG.Walter.Ree.T2

open CFSG.Walter.Ward CFSG.Walter.J1Recog Word BaseRel
open scoped Pointwise

section Thompson

variable {k : Type} [Field k] [CharP k 3] (σ : k ≃+* k) (d : k)

theorem two_ne_zero_of_charThree : (2 : k) ≠ 0 := by
  intro h
  have h3 := three_eq_zero' (k := k)
  exact one_ne_zero (by linear_combination h3 - h)

theorem thompsonJ_ne_one : ThompsonN.J σ ≠ 1 := by
  intro h
  have h1 : ((ThompsonN.J σ).κ : k) = ((1 : ThompsonN k σ).κ : k) := by rw [h]
  simp only [ThompsonN.J, ThompsonN.torus_κ, ThompsonN.one_κ, Units.val_neg, Units.val_one] at h1
  exact two_ne_zero_of_charThree (by linear_combination -h1)

theorem tY_ne_one : tY σ d ≠ 1 := by
  intro h
  have h1 := congrArg ThompsonN.α h
  simp [tY, pp] at h1

theorem thompsonJ_sq : ThompsonN.J σ ^ 2 = 1 := by
  rw [ThompsonN.J, ← map_pow, neg_one_sq, map_one]

theorem tT_pow_three : tT σ ^ 3 = 1 := by
  rw [pow_three', tT, pp, ThompsonN.mul_P, ThompsonN.mul_P]
  have h3 := three_eq_zero' (k := k)
  ext
  · rfl
  · simp
  · simp only [map_zero, mul_zero, sub_zero, add_zero, ThompsonN.one_β]
    linear_combination h3
  · simp

theorem tY_pow_nine : tY σ d ^ 9 = 1 := by
  rw [show 9 = 3 * 3 from rfl, pow_mul, tY_cube, pow_three', pp, ThompsonN.mul_P,
    ThompsonN.mul_P]
  have h3 := three_eq_zero' (k := k)
  ext
  · rfl
  · simp
  · simp
  · simp only [map_zero, mul_zero, sub_zero, add_zero, zero_pow two_ne_zero, ThompsonN.one_γ]
    linear_combination h3

theorem thompsonJ_conj_tT : (ThompsonN.J σ)⁻¹ * tT σ * ThompsonN.J σ = tT σ := by
  rw [tT, pp, ThompsonN.J_conj, neg_zero]

theorem thompsonJ_conj_tY : (ThompsonN.J σ)⁻¹ * tY σ d * ThompsonN.J σ = (tY σ d)⁻¹ := by
  rw [tY, pp, ThompsonN.J_conj, ThompsonN.inv_P]
  ext <;> simp

theorem tT_conj_tY : (tT σ)⁻¹ * tY σ d * tT σ = (tY σ d ^ 2)⁻¹ := by
  rw [mul_assoc, tY_mul_tT, tY_sq]
  simp only [tT, pp]
  rw [ThompsonN.inv_P, ThompsonN.inv_P, ThompsonN.mul_P]
  ext
  · rfl
  · simp
  · simp
  · simp only [map_zero, map_one, mul_zero, sub_zero, add_zero, mul_one, neg_zero,
      zero_pow two_ne_zero, one_pow]
    ring


end Thompson

section Gens

variable {k : Type} [Field k] [CharP k 3] {σ : k ≃+* k} {G : Type} [Group G]

theorem incl_injective {N : Subgroup G} (e : N ≃* ThompsonN k σ) : Function.Injective (incl e) :=
  fun _ _ h => e.symm.injective (Subtype.ext h)

theorem incl_mem {N : Subgroup G} (e : N ≃* ThompsonN k σ) (n : ThompsonN k σ) : incl e n ∈ N :=
  (e.symm n).2

@[expose] noncomputable def baseGens {N : Subgroup G} (e : N ≃* ThompsonN k σ) (K : G) (d : k) :
    Fin 4 → G :=
  ![incl e (ThompsonN.J σ), K, incl e (tT σ), incl e (tY σ d)]

variable {N : Subgroup G} (e : N ≃* ThompsonN k σ) (K : G) (d : k)

theorem baseGens_zero : baseGens e K d 0 = incl e (ThompsonN.J σ) := rfl


end Gens

section Centralizer

variable {k : Type} [Field k] [CharP k 3] {σ : k ≃+* k} {G : Type} [Group G] [Finite G]


end Centralizer

section Base

variable {k : Type} [Field k] [CharP k 3] {σ : k ≃+* k} {G : Type} [Group G]
variable {N : Subgroup G} {e : N ≃* ThompsonN k σ} {K : G} {d : k}


noncomputable def baseHom (hf : ∀ w ∈ rels1512, ev (baseGens e K d) w = 1) : PGammaL28 →* G :=
  (lift rels1512 (baseGens e K d) hf).comp iso1512.symm.toMonoidHom

variable (hf : ∀ w ∈ rels1512, ev (baseGens e K d) w = 1)

theorem baseHom_j : baseHom hf PGammaL28.j = incl e (ThompsonN.J σ) := by
  simp only [baseHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, iso1512_symm_j, lift_of,
    baseGens_zero]


theorem baseHom_injective : Function.Injective (baseHom hf) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  by_contra ha1
  have hj := j_mem_of_normal (MonoidHom.normal_ker (baseHom hf)) (MonoidHom.mem_ker.mpr ha) ha1
  rw [MonoidHom.mem_ker, baseHom_j] at hj
  exact thompsonJ_ne_one σ (incl_injective e (hj.trans (map_one _).symm))

end Base


end CFSG.Walter.Ree.T2
