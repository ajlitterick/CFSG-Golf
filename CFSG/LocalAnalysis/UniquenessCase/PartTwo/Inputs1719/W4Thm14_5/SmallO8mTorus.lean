module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallO8mShortSection

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5.SmallO8mTorus

open Module QuadraticMap CFSG.LieType.Universal.Spin
open CFSG.LieType.Universal.Spin.Twisted

section QuadraticField

variable {K : Type} [Field K] {b c : K}

private theorem starCoord_eq_fieldCoord (x : ShortField b c) :
    starCoord x = fieldCoord (-star x) := by
  ext i
  fin_cases i <;> simp [starCoord, fieldCoord, QuadraticAlgebra.re_star, QuadraticAlgebra.im_star]

variable [Fact (∀ r : K, r ^ 2 ≠ -c + b * r)]

theorem planeRefl_fieldCoord (t : (ShortField b c)ˣ) (x : ShortField b c) :
    planeRefl b c (fieldCoord (t : ShortField b c)) (fieldCoord x) =
      fieldCoord (-((t : ShortField b c) / star (t : ShortField b c)) * star x) := by
  have hn : QuadraticAlgebra.norm (t : ShortField b c) ≠ 0 :=
    (QuadraticAlgebra.norm_eq_zero_iff_eq_zero).not.mpr t.ne_zero
  have hnorm := QuadraticAlgebra.algebraMap_norm_eq_mul_star (t : ShortField b c)
  have hinv : (star (t : ShortField b c))⁻¹ =
      (t : ShortField b c) * algebraMap K (ShortField b c) (QuadraticAlgebra.norm (t : ShortField b c))⁻¹ := by
    apply mul_left_cancel₀ (star_ne_zero.mpr t.ne_zero)
    rw [mul_inv_cancel₀ (star_ne_zero.mpr t.ne_zero)]
    rw [← mul_assoc, mul_comm (star (t : ShortField b c)) (t : ShortField b c), ← hnorm,
      ← map_mul, mul_inv_cancel₀ hn, map_one]
  rw [div_eq_mul_inv, hinv]
  simp only [planeRefl, planeNorm_fieldCoord]
  ext i
  fin_cases i <;>
    simp [fieldCoord, polarPlane,
      QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, QuadraticAlgebra.re_star,
      QuadraticAlgebra.im_star] <;>
    field_simp <;> rw [QuadraticAlgebra.norm_def] <;> ring

theorem planeRefl_comp_fieldCoord (t : (ShortField b c)ˣ) (x : ShortField b c) :
    planeRefl b c (fieldCoord (t : ShortField b c))
        (planeRefl b c planeOne (fieldCoord x)) =
      fieldCoord ((t : ShortField b c) / star (t : ShortField b c) * x) := by
  have h1 := planeRefl_fieldCoord (b := b) (c := c) (1 : (ShortField b c)ˣ) x
  simp only [Units.val_one, star_one, div_one, neg_one_mul] at h1
  rw [fieldCoord_one] at h1
  rw [h1, planeRefl_fieldCoord]
  simp [star_neg, star_star]

variable [Finite K] [CharP K 2]


theorem star_shortField_eq_pow {e : ℕ} (_he : 2 ≤ e) (hK : Nat.card K = 2 ^ e)
    (x : ShortField b c) : star x = x ^ (2 ^ e) := by
  let σ : ShortField b c ≃ₐ[K] ShortField b c :=
    { toFun := star
      invFun := star
      left_inv := star_star
      right_inv := star_star
      map_mul' := fun x y => by rw [star_mul, mul_comm]
      map_add' := star_add
      commutes' := fun r => by ext <;> simp [QuadraticAlgebra.re_star, QuadraticAlgebra.im_star] }
  have hb : b ≠ 0 := by
    intro hb
    obtain ⟨r, hr⟩ := isSquare_of_charTwo' (-c)
    exact (Fact.out : ∀ r : K, r ^ 2 ≠ -c + b * r) r (by simpa [hb, pow_two] using hr.symm)
  have hσ : σ ≠ 1 := by
    intro h
    have h' := congrArg (fun f : ShortField b c ≃ₐ[K] ShortField b c =>
      (f (QuadraticAlgebra.omega : ShortField b c)).re) h
    simp [σ, QuadraticAlgebra.re_star] at h'
    exact hb h'
  let : Fintype K := Fintype.ofFinite K
  have h := CFSG.LocalAnalysis.eq_pow_card_of_ne_one
    (QuadraticAlgebra.finrank_eq_two (R := K) (a := -c) (b := b)) hσ x
  change star x = _ at h
  rw [← Nat.card_eq_fintype_card, hK] at h
  exact h

end QuadraticField

section Spin

variable {K : Type} [Field K] [Finite K] {b c : K}
  (hirrQ : ∀ r : K, r ^ 2 + b * r + c ≠ 0)

theorem shortTorusHom_conj_shortX {i j : Fin 3} (hij : j ≠ i)
    (t : (ShortField b c)ˣ) (x : ShortField b c) :
    shortTorusHom 4 hirrQ i t * shortX 4 hirrQ j x * (shortTorusHom 4 hirrQ i t)⁻¹ =
      shortX 4 hirrQ j ((t : ShortField b c) / star (t : ShortField b c) * x) := by
  have := fact_shortField hirrQ
  rw [shortTorusHom_apply, shortX,
    shortTorusElt_conj_shortPosHom_of_ne 4 hirrQ hij (fieldCoord_ne_zero t.ne_zero),
    planeRefl_comp_fieldCoord, shortX]

theorem shortTorusHom_conj_shortY {i j : Fin 3} (hij : j ≠ i)
    (t : (ShortField b c)ˣ) (x : ShortField b c) :
    shortTorusHom 4 hirrQ i t * shortY 4 hirrQ j x * (shortTorusHom 4 hirrQ i t)⁻¹ =
      shortY 4 hirrQ j (star (t : ShortField b c) / (t : ShortField b c) * x) := by
  have := fact_shortField hirrQ
  rw [shortTorusHom_apply, shortY, starCoord_eq_fieldCoord,
    shortTorusElt_conj_shortNegHom_of_ne 4 hirrQ hij (fieldCoord_ne_zero t.ne_zero),
    planeRefl_comp_fieldCoord, shortY, starCoord_eq_fieldCoord]
  congr 2
  simp [div_eq_mul_inv, star_mul, mul_comm, mul_left_comm]

variable [CharP K 2]

theorem shortTorusHom_mul_inv {i j : Fin 3} (hij : i ≠ j)
    (t : (ShortField b c)ˣ) :
    shortTorusHom 4 hirrQ i t * (shortTorusHom 4 hirrQ j t)⁻¹ =
      (minusFrame 4 b c).longTorus hij true false (Units.map QuadraticAlgebra.norm t) := by
  have := fact_shortField hirrQ
  have hfaith : Function.Injective (spinAction (quadMinus 4 K b c)) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rw [← ker_spinMatrix, ker_spinMatrix_quadMinus_eq_bot hirrQ CharTwo.two_eq_zero]
  have ha := fieldCoord_ne_zero t.ne_zero
  have hn : QuadraticAlgebra.norm (t : ShortField b c) ≠ 0 :=
    (QuadraticAlgebra.norm_eq_zero_iff_eq_zero).not.mpr t.ne_zero
  rw [mul_inv_eq_iff_eq_mul]
  apply hfaith
  rw [shortTorusHom_apply, shortTorusHom_apply, map_mul]
  have hf : ∀ m r,
      spinAction (quadMinus 4 K b c) (shortTorusElt 4 hirrQ i (fieldCoord (t : ShortField b c)))
          (minusVec 4 m r) =
        (spinAction (quadMinus 4 K b c)
          ((minusFrame 4 b c).longTorus hij true false (Units.map QuadraticAlgebra.norm t)) *
          spinAction (quadMinus 4 K b c)
            (shortTorusElt 4 hirrQ j (fieldCoord (t : ShortField b c)))) (minusVec 4 m r) := by
    intro m r
    rw [LinearEquiv.mul_apply, spinAction_shortTorusElt_minusVec 4 hirrQ i ha,
      spinAction_shortTorusElt_minusVec 4 hirrQ j ha, map_smul,
      ← minusFrame_vec, HypFrame.spinAction_longTorus_vec, minusFrame_vec, smul_smul]
    cases r <;> by_cases hmi : m = i <;> by_cases hmj : m = j
    all_goals simp [shortTorusScalar, longCoroot, hmi, hmj, hij, hij.symm,
      planeNorm_fieldCoord, Units.val_inv_eq_inv_val, hn] at *
  have hp : ∀ p,
      spinAction (quadMinus 4 K b c) (shortTorusElt 4 hirrQ i (fieldCoord (t : ShortField b c)))
          (planeVec 4 p) =
        (spinAction (quadMinus 4 K b c)
          ((minusFrame 4 b c).longTorus hij true false (Units.map QuadraticAlgebra.norm t)) *
          spinAction (quadMinus 4 K b c)
            (shortTorusElt 4 hirrQ j (fieldCoord (t : ShortField b c)))) (planeVec 4 p) := by
    intro p
    rw [LinearEquiv.mul_apply, spinAction_shortTorusElt_planeVec 4 hirrQ i ha,
      spinAction_shortTorusElt_planeVec 4 hirrQ j ha, spinAction_longTorus_planeVec]
  apply LinearEquiv.toLinearMap_injective
  refine LinearMap.pi_ext fun x a => ?_
  rw [show (Pi.single x a : Vm 4 K) = a • Pi.single x 1 by
    funext y
    by_cases h : y = x <;> simp [h]]
  simp only [LinearEquiv.coe_coe, map_smul]
  congr 1
  rcases x with m | m | s
  · exact hf m true
  · exact hf m false
  · have hs : (Pi.single (.inr (.inr s)) 1 : Vm 4 K) = planeVec 4 (Pi.single s 1) := by
      funext x
      rcases x with k | k | s' <;> simp [planeVec, Pi.single_apply]
    rw [hs, hp]


theorem shortTorusHom_mem_H (i : Fin 3) (t : (ShortField b c)ˣ) :
    shortTorusHom 4 hirrQ i t ∈ (SmallO8mCurtis.curtisDatum 4 (by norm_num) hirrQ).H := by
  have h2 : shortTorusHom 4 hirrQ 2 t ∈
      (SmallO8mCurtis.curtisDatum 4 (by norm_num) hirrQ).H := by
    refine Subgroup.mem_iSup_of_mem (2 : Fin 3) ?_
    rw [minusTorus_of_not_lt 4 hirrQ (k := (2 : Fin 3)) (by norm_num),
      ← range_shortTorusHom]
    exact ⟨t, rfl⟩
  have step : ∀ k : Fin 3, ∀ hk : k.val + 1 < 3,
      shortTorusHom 4 hirrQ ⟨k.val + 1, hk⟩ t ∈
          (SmallO8mCurtis.curtisDatum 4 (by norm_num) hirrQ).H →
        shortTorusHom 4 hirrQ k t ∈
          (SmallO8mCurtis.curtisDatum 4 (by norm_num) hirrQ).H := by
    intro k hk hnext
    have hlong : (minusFrame 4 b c).longTorus (succ_ne_of_lt 4 hk) true false
        (Units.map QuadraticAlgebra.norm t) ∈
          (SmallO8mCurtis.curtisDatum 4 (by norm_num) hirrQ).H := by
      refine Subgroup.mem_iSup_of_mem k ?_
      rw [minusTorus_of_lt 4 hirrQ hk]
      exact ⟨Units.map QuadraticAlgebra.norm t, rfl⟩
    have heq := (mul_inv_eq_iff_eq_mul).mp
      (shortTorusHom_mul_inv hirrQ (succ_ne_of_lt 4 hk) t)
    rw [heq]
    exact mul_mem hlong hnext
  have h1 := step 1 (by norm_num) h2
  have h0 := step 0 (by norm_num) h1
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

theorem exists_shortTorusHom_mul_inv_mem_centralizer {i j : Fin 3} (hij : i ≠ j)
    (t : (ShortField b c)ˣ) :
    ∃ z : (ShortField b c)ˣ,
      (z : ShortField b c) ^ 2 = (t : ShortField b c) / star (t : ShortField b c) ∧
        shortTorusHom 4 hirrQ i t * (shortTorusHom 4 hirrQ j z)⁻¹ ∈ Subgroup.centralizer
          ((((shortPosHom 4 hirrQ j).range ⊔ (shortNegHom 4 hirrQ j).range) :
            Subgroup (spinGroup (quadMinus 4 K b c))) : Set _) := by
  have := fact_shortField hirrQ
  have := finite_shortField (b := b) (c := c)
  have : CharP (ShortField b c) 2 :=
    charP_of_injective_algebraMap (algebraMap K (ShortField b c)).injective 2
  obtain ⟨r, hr⟩ := isSquare_of_charTwo'
    ((t : ShortField b c) / star (t : ShortField b c))
  have hr0 : r ≠ 0 := by
    intro h
    simp [h] at hr
  let z : (ShortField b c)ˣ := Units.mk0 r hr0
  have hz : (z : ShortField b c) ^ 2 =
      (t : ShortField b c) / star (t : ShortField b c) := by simpa [z, pow_two] using hr.symm
  have hzi : star (t : ShortField b c) / (t : ShortField b c) =
      ((z : ShortField b c) ^ 2)⁻¹ := by
    rw [hz]
    simp [div_eq_mul_inv, mul_comm]
  refine ⟨z, hz, ?_⟩
  let R := shortRels 4 hirrQ j
  have hinv : (shortTorusHom 4 hirrQ j z)⁻¹ = R.h ((z : ShortField b c)⁻¹) := by
    rw [← map_inv, shortTorusHom_apply, ← shortRels_h, Units.val_inv_eq_inv_val]
  have hX : ∀ x : ShortField b c,
      (shortTorusHom 4 hirrQ i t * (shortTorusHom 4 hirrQ j z)⁻¹) * R.x x *
          (shortTorusHom 4 hirrQ i t * (shortTorusHom 4 hirrQ j z)⁻¹)⁻¹ = R.x x := by
    intro x
    calc
      _ = shortTorusHom 4 hirrQ i t *
          (R.h ((z : ShortField b c)⁻¹) * R.x x * (R.h ((z : ShortField b c)⁻¹))⁻¹) *
          (shortTorusHom 4 hirrQ i t)⁻¹ := by rw [hinv]; group
      _ = shortTorusHom 4 hirrQ i t * R.x ((z : ShortField b c)⁻¹ ^ 2 * x) *
          (shortTorusHom 4 hirrQ i t)⁻¹ := by rw [R.h_conj_x (inv_ne_zero z.ne_zero)]
      _ = R.x x := by
        change shortTorusHom 4 hirrQ i t * shortX 4 hirrQ j _ *
          (shortTorusHom 4 hirrQ i t)⁻¹ = shortX 4 hirrQ j x
        rw [shortTorusHom_conj_shortX hirrQ hij.symm]
        congr 1
        rw [← hz, inv_pow, mul_inv_cancel_left₀ (pow_ne_zero 2 z.ne_zero)]
  have hY : ∀ x : ShortField b c,
      (shortTorusHom 4 hirrQ i t * (shortTorusHom 4 hirrQ j z)⁻¹) * R.y x *
          (shortTorusHom 4 hirrQ i t * (shortTorusHom 4 hirrQ j z)⁻¹)⁻¹ = R.y x := by
    intro x
    calc
      _ = shortTorusHom 4 hirrQ i t *
          (R.h ((z : ShortField b c)⁻¹) * R.y x * (R.h ((z : ShortField b c)⁻¹))⁻¹) *
          (shortTorusHom 4 hirrQ i t)⁻¹ := by rw [hinv]; group
      _ = shortTorusHom 4 hirrQ i t * R.y (((z : ShortField b c)⁻¹ ^ 2)⁻¹ * x) *
          (shortTorusHom 4 hirrQ i t)⁻¹ := by rw [R.h_conj_y (inv_ne_zero z.ne_zero)]
      _ = R.y x := by
        change shortTorusHom 4 hirrQ i t * shortY 4 hirrQ j _ *
          (shortTorusHom 4 hirrQ i t)⁻¹ = shortY 4 hirrQ j x
        rw [shortTorusHom_conj_shortY hirrQ hij.symm]
        congr 1
        rw [hzi, inv_pow, inv_inv, inv_mul_cancel_left₀ (pow_ne_zero 2 z.ne_zero)]
  apply Subgroup.mem_centralizer_iff.mpr
  intro g hg
  have hgR : g ∈ R.sub := by rwa [shortRels_sub]
  exact (R.commute_of_forall hX hY hgR).eq.symm

theorem exists_longTorus_mul_inv_mem_centralizer (a : Kˣ) :
    ∃ z : Kˣ, (z : K) ^ 2 = (a : K) ∧
      (minusFrame 4 b c).longTorus (by decide : (1 : Fin 3) ≠ 2) true true a *
          (shortTorusHom 4 hirrQ 2
            (Units.map (algebraMap K (ShortField b c)).toMonoidHom z))⁻¹ ∈ Subgroup.centralizer
        ((((shortPosHom 4 hirrQ 2).range ⊔ (shortNegHom 4 hirrQ 2).range) :
          Subgroup (spinGroup (quadMinus 4 K b c))) : Set _) := by
  have := fact_shortField hirrQ
  obtain ⟨r, hr⟩ := isSquare_of_charTwo' (a : K)
  have hr0 : r ≠ 0 := by
    intro h
    simp [h] at hr
  let z : Kˣ := Units.mk0 r hr0
  let zE := Units.map (algebraMap K (ShortField b c)).toMonoidHom z
  have hz : (z : K) ^ 2 = (a : K) := by simpa [z, pow_two] using hr.symm
  have hzE : (zE : ShortField b c) ^ 2 = algebraMap K (ShortField b c) (a : K) := by
    change (algebraMap K (ShortField b c) (z : K)) ^ 2 = _
    rw [← map_pow, hz]
  refine ⟨z, hz, ?_⟩
  apply SmallO8mShortSection.mul_shortTorus_inv_mem_centralizer_of_conj hirrQ _ zE
  · intro x
    change (minusFrame 4 b c).longTorus _ true true a *
        twShortRoot 4 hirrQ 2 true (.ofAdd (fieldCoord x)) * _ =
      twShortRoot 4 hirrQ 2 true (.ofAdd (fieldCoord ((zE : ShortField b c) ^ 2 * x)))
    rw [longTorus_conj_twShortRoot]
    congr 2
    rw [hzE, fieldCoord_algebraMap_mul]
    simp [longCoroot]
  · intro x
    change (minusFrame 4 b c).longTorus _ true true a *
        twShortRoot 4 hirrQ 2 false (.ofAdd (starCoord x)) * _ =
      twShortRoot 4 hirrQ 2 false (.ofAdd (starCoord (((zE : ShortField b c) ^ 2)⁻¹ * x)))
    rw [longTorus_conj_twShortRoot]
    congr 2
    rw [hzE, ← map_inv₀]
    have hcoord : starCoord (algebraMap K (ShortField b c) ((a : K)⁻¹) * x) =
        (a : K)⁻¹ • starCoord x := by
      rw [QuadraticAlgebra.algebraMap_eq]
      ext k
      fin_cases k <;> simp [starCoord]
      ring
    rw [hcoord]
    simp [longCoroot, Units.val_inv_eq_inv_val]

end Spin

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5.SmallO8mTorus
