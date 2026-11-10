module

public import CFSG.RankThree.GF2n.Smith81.S81E7Basic
public import CFSG.LieType.Steinberg.Minuscule.RankOne

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.E7Model

open CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley

@[expose] def V0 (K : Type) [Field K] : Submodule K (V K) := Finsupp.supported K K (idx0 : Set (Fin e7Data.d))

theorem mem_V0 {K : Type} [Field K] {v : V K} : v ∈ V0 K ↔ ∀ b, b ∉ idx0 → v b = 0 := by
  unfold V0
  rw [Finsupp.mem_supported']
  simp

variable {K : Type} [Field K]

@[expose] def jFun (m : Matrix (Fin 2) (Fin 2) K) (v : Fin e7Data.d → K) (b : Fin e7Data.d) : K :=
  if pr b theta = 0 then v b
  else if pr b theta = -1 then m 0 0 * v b + m 0 1 * v (shift theta b)
  else m 1 0 * v (shift (-theta) b) + m 1 1 * v b

@[expose] def jOp (m : Matrix (Fin 2) (Fin 2) K) : V K →ₗ[K] V K where
  toFun v := Finsupp.equivFunOnFinite.symm (jFun m ⇑v)
  map_add' v w := by
    ext b
    simp only [Finsupp.equivFunOnFinite_symm_apply_apply, Finsupp.coe_add, Pi.add_apply, jFun]
    split_ifs <;> ring
  map_smul' c v := by
    ext b
    simp only [Finsupp.equivFunOnFinite_symm_apply_apply, Finsupp.coe_smul, Pi.smul_apply,
      smul_eq_mul, RingHom.id_apply, jFun]
    split_ifs <;> ring

theorem jOp_apply (m : Matrix (Fin 2) (Fin 2) K) (v : V K) (b : Fin e7Data.d) :
    jOp m v b = jFun m ⇑v b := by
  simp [jOp]

theorem jFun_of_zero {m : Matrix (Fin 2) (Fin 2) K} {v : Fin e7Data.d → K} {b : Fin e7Data.d}
    (h : pr b theta = 0) : jFun m v b = v b := by
  unfold jFun
  rw [if_pos h]

theorem jFun_of_neg {m : Matrix (Fin 2) (Fin 2) K} {v : Fin e7Data.d → K} {b : Fin e7Data.d}
    (h : pr b theta = -1) :
    jFun m v b = m 0 0 * v b + m 0 1 * v (shift theta b) := by
  unfold jFun
  rw [if_neg (show ¬ (pr b theta = 0) by omega), if_pos h]

theorem jFun_of_pos {m : Matrix (Fin 2) (Fin 2) K} {v : Fin e7Data.d → K} {b : Fin e7Data.d}
    (h : pr b theta = 1) :
    jFun m v b = m 1 0 * v (shift (-theta) b) + m 1 1 * v b := by
  unfold jFun
  rw [if_neg (show ¬ (pr b theta = 0) by omega), if_neg (show ¬ (pr b theta = -1) by omega)]

theorem jOp_one : jOp (1 : Matrix (Fin 2) (Fin 2) K) = 1 := by
  apply LinearMap.ext
  intro v
  apply Finsupp.ext
  intro b
  rw [jOp_apply, Module.End.one_apply]
  rcases pr_mem isRoot_theta b with h | h | h
  · rw [jFun_of_neg h]
    simp [Matrix.one_apply]
  · rw [jFun_of_zero h]
  · rw [jFun_of_pos h]
    simp [Matrix.one_apply]

theorem jOp_mul (m m' : Matrix (Fin 2) (Fin 2) K) : jOp (m * m') = jOp m * jOp m' := by
  apply LinearMap.ext
  intro v
  apply Finsupp.ext
  intro b
  have hw : ⇑(jOp m' v) = jFun m' ⇑v := funext fun c => jOp_apply m' v c
  rw [Module.End.mul_apply, jOp_apply, jOp_apply, hw]
  rcases pr_mem isRoot_theta b with h | h | h
  · simp only [jFun_of_neg h, jFun_of_pos (pr_shift_self isRoot_theta h),
      shift_neg_shift isRoot_theta h, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  · simp only [jFun_of_zero h]
  · simp only [jFun_of_pos h, jFun_of_neg (pr_shift_neg isRoot_theta h),
      shift_shift_neg isRoot_theta h, Matrix.mul_apply, Fin.sum_univ_two]
    ring

@[expose] def jHom : Matrix.SpecialLinearGroup (Fin 2) K →* (Module.End K (V K))ˣ where
  toFun m := ⟨jOp (m : Matrix (Fin 2) (Fin 2) K), jOp ((m⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K), by rw [← jOp_mul, ← Matrix.SpecialLinearGroup.coe_mul,
        mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one, jOp_one], by
      rw [← jOp_mul, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
        Matrix.SpecialLinearGroup.coe_one, jOp_one]⟩
  map_one' := by
    ext1
    simp [jOp_one]
  map_mul' m m' := by
    ext1
    simp [jOp_mul]

theorem jHom_val (m : Matrix.SpecialLinearGroup (Fin 2) K) :
    ((jHom m : (Module.End K (V K))ˣ) : Module.End K (V K)) = jOp (m : Matrix (Fin 2) (Fin 2) K) :=
  rfl

theorem xu_theta [CharP K 2] (c : K) : e7Data_valid.xu K theta c = jHom (MinData.Valid.slLower K c) := by
  apply Units.ext
  apply LinearMap.ext
  intro v
  apply Finsupp.ext
  intro b
  rw [xu_apply_coord isRoot_theta, jHom_val, jOp_apply, MinData.Valid.slLower_val]
  unfold jFun
  rcases pr_mem isRoot_theta b with h | h | h <;> simp [h] <;> ring

theorem xu_neg_theta [CharP K 2] (c : K) : e7Data_valid.xu K (-theta) c = jHom (MinData.Valid.slUpper K c) := by
  apply Units.ext
  apply LinearMap.ext
  intro v
  apply Finsupp.ext
  intro b
  rw [xu_apply_coord (isRoot_neg isRoot_theta), jHom_val, jOp_apply, MinData.Valid.slUpper_val,
    neg_neg, pr_neg]
  unfold jFun
  rcases pr_mem isRoot_theta b with h | h | h <;> simp [h] <;> ring

@[expose] def Jgrp (K : Type) [Field K] : Subgroup (Module.End K (V K))ˣ :=
  Subgroup.closure {g | ∃ c : K, g = e7Data_valid.xu K theta c ∨ g = e7Data_valid.xu K (-theta) c}

private theorem sl2_eq_upper_lower_upper (s : Matrix.SpecialLinearGroup (Fin 2) K)
    (h : (s : Matrix (Fin 2) (Fin 2) K) 1 0 ≠ 0) :
    s = MinData.Valid.slUpper K (((s : Matrix (Fin 2) (Fin 2) K) 0 0 - 1) /
        (s : Matrix (Fin 2) (Fin 2) K) 1 0) *
      MinData.Valid.slLower K ((s : Matrix (Fin 2) (Fin 2) K) 1 0) *
      MinData.Valid.slUpper K (((s : Matrix (Fin 2) (Fin 2) K) 1 1 - 1) /
        (s : Matrix (Fin 2) (Fin 2) K) 1 0) := by
  have hdet := s.2
  rw [Matrix.det_fin_two] at hdet
  ext x y
  simp only [Matrix.SpecialLinearGroup.coe_mul, MinData.Valid.slUpper_val,
    MinData.Valid.slLower_val]
  fin_cases x <;> fin_cases y
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    field_simp
    ring
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    field_simp
    linear_combination (-1 : K) * hdet
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    field_simp
    ring

theorem sl2_eq_prod (m : Matrix.SpecialLinearGroup (Fin 2) K) :
    ∃ e a b c : K, m = MinData.Valid.slLower K e * MinData.Valid.slUpper K a * MinData.Valid.slLower K b * MinData.Valid.slUpper K c := by
  have hlow0 : MinData.Valid.slLower K (0 : K) = 1 := by
    ext x y
    fin_cases x <;> fin_cases y <;> rfl
  by_cases h : (m : Matrix (Fin 2) (Fin 2) K) 1 0 = 0
  · set s' := MinData.Valid.slLower K (1 : K) * m with hs'_def
    have hdet := m.2
    rw [Matrix.det_fin_two, h, mul_zero, sub_zero] at hdet
    have h' : (s' : Matrix (Fin 2) (Fin 2) K) 1 0 ≠ 0 := by
      simp only [s', Matrix.SpecialLinearGroup.coe_mul, MinData.Valid.slLower_val, Matrix.mul_apply,
        Fin.sum_univ_two]
      simp [h]
      exact left_ne_zero_of_mul_eq_one hdet
    have hs' := sl2_eq_upper_lower_upper s' h'
    refine ⟨-1, ((s' : Matrix (Fin 2) (Fin 2) K) 0 0 - 1) / (s' : Matrix (Fin 2) (Fin 2) K) 1 0,
      (s' : Matrix (Fin 2) (Fin 2) K) 1 0,
      ((s' : Matrix (Fin 2) (Fin 2) K) 1 1 - 1) / (s' : Matrix (Fin 2) (Fin 2) K) 1 0, ?_⟩
    rw [mul_assoc, mul_assoc, ← mul_assoc (MinData.Valid.slUpper K _), ← hs', hs'_def, ← mul_assoc,
      show MinData.Valid.slLower K (-1 : K) * MinData.Valid.slLower K 1 = 1 by
        ext x y
        fin_cases x <;> fin_cases y <;>
          simp [Matrix.mul_apply, Fin.sum_univ_two, MinData.Valid.slLower_val],
      one_mul]
  · refine ⟨0, ((m : Matrix (Fin 2) (Fin 2) K) 0 0 - 1) / (m : Matrix (Fin 2) (Fin 2) K) 1 0,
      (m : Matrix (Fin 2) (Fin 2) K) 1 0,
      ((m : Matrix (Fin 2) (Fin 2) K) 1 1 - 1) / (m : Matrix (Fin 2) (Fin 2) K) 1 0, ?_⟩
    rw [hlow0, one_mul]
    exact sl2_eq_upper_lower_upper m h

theorem Jgrp_eq_range [CharP K 2] : Jgrp K = (jHom (K := K)).range := by
  apply le_antisymm
  · rw [Jgrp, Subgroup.closure_le]
    rintro g ⟨c, rfl | rfl⟩
    · exact MonoidHom.mem_range.2 ⟨MinData.Valid.slLower K c, (xu_theta c).symm⟩
    · exact MonoidHom.mem_range.2 ⟨MinData.Valid.slUpper K c, (xu_neg_theta c).symm⟩
  · rintro g ⟨m, rfl⟩
    obtain ⟨e, a, b, c, rfl⟩ := sl2_eq_prod m
    have h1 : jHom (MinData.Valid.slLower K e) ∈ Jgrp K := by
      rw [← xu_theta]
      exact Subgroup.subset_closure ⟨e, Or.inl rfl⟩
    have h2 : jHom (MinData.Valid.slUpper K a) ∈ Jgrp K := by
      rw [← xu_neg_theta]
      exact Subgroup.subset_closure ⟨a, Or.inr rfl⟩
    have h3 : jHom (MinData.Valid.slLower K b) ∈ Jgrp K := by
      rw [← xu_theta]
      exact Subgroup.subset_closure ⟨b, Or.inl rfl⟩
    have h4 : jHom (MinData.Valid.slUpper K c) ∈ Jgrp K := by
      rw [← xu_neg_theta]
      exact Subgroup.subset_closure ⟨c, Or.inr rfl⟩
    rw [map_mul, map_mul, map_mul]
    exact mul_mem (mul_mem (mul_mem h1 h2) h3) h4


@[expose] def IsRootElt (g : (Module.End K (V K))ˣ) : Prop :=
  ∃ h ∈ EGrp K, ∃ (γ : Fin (Tag.rank .E7) → ℤ) (c : K), IsRoot .E7 γ ∧ c ≠ 0 ∧
    g = h * e7Data_valid.xu K γ c * h⁻¹


theorem rootOp_range_eq_supported [CharP K 2] {γ : Fin (Tag.rank .E7) → ℤ} (hγ : IsRoot .E7 γ) :
    LinearMap.range (e7Data.rootOp K γ) =
      Finsupp.supported K K ((Finset.univ.filter fun b : Fin e7Data.d => pr b γ = 1 :
        Finset (Fin e7Data.d)) : Set (Fin e7Data.d)) := by
  apply le_antisymm
  · rintro w ⟨v, rfl⟩
    rw [Finsupp.mem_supported']
    intro b hb
    have hb' : ¬ pr b γ = 1 := fun h =>
      hb (Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩))
    rw [rootOp_apply hγ, if_neg hb']
  · intro w hw
    rw [Finsupp.mem_supported'] at hw
    refine ⟨Finsupp.equivFunOnFinite.symm (fun a => if pr a γ = -1 then w (shift γ a) else 0), ?_⟩
    ext b
    rw [rootOp_apply hγ]
    by_cases hb : pr b γ = 1
    · rw [if_pos hb]
      simp only [Finsupp.equivFunOnFinite_symm_apply_apply]
      rw [if_pos (pr_shift_neg hγ hb), shift_shift_neg hγ hb]
    · rw [if_neg hb]
      have hb'' : b ∉ ((Finset.univ.filter fun b : Fin e7Data.d => pr b γ = 1 :
          Finset (Fin e7Data.d)) : Set (Fin e7Data.d)) :=
        fun h => hb (Finset.mem_filter.1 (Finset.mem_coe.1 h)).2
      exact (hw b hb'').symm


end CFSG.RankThree.GF2n.Smith81.E7Model
