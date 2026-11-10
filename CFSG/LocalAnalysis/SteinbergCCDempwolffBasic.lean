module

public import CFSG.LieType.Steinberg.Classical.SpecialLinearSteinberg
public import CFSG.GroupTheory.GLnTwoSplitting.Cohomology

public section

namespace CFSG.LocalAnalysis.DempwolffFive

open Matrix

abbrev G := GL (Fin 5) (ZMod 2)

abbrev Sym := Fin 5 × Fin 5 × ZMod 2

@[expose] def symMat (s : Sym) : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  if s.1 = s.2.1 then 1 else Matrix.transvection s.1 s.2.1 s.2.2

theorem symMat_mul_self (s : Sym) : symMat s * symMat s = 1 := by
  unfold symMat
  split_ifs with h
  · exact mul_one 1
  · rw [Matrix.transvection_mul_transvection_same _ _ h, CharTwo.add_self_eq_zero,
      Matrix.transvection_zero]

@[expose] def xg (s : Sym) : G :=
  ⟨symMat s, symMat s, symMat_mul_self s, symMat_mul_self s⟩


theorem zmod_two_eq_one_of_isUnit {x : ZMod 2} (h : IsUnit x) : x = 1 := by
  fin_cases x
  · exact absurd h not_isUnit_zero
  · rfl

theorem toGL_surjective :
    Function.Surjective (Matrix.SpecialLinearGroup.toGL (n := Fin 5) (R := ZMod 2)) := by
  intro g
  have hdet : (g : Matrix (Fin 5) (Fin 5) (ZMod 2)).det = 1 :=
    zmod_two_eq_one_of_isUnit (Matrix.isUnits_det_units g)
  refine ⟨⟨(g : Matrix (Fin 5) (Fin 5) (ZMod 2)), hdet⟩, ?_⟩
  exact Matrix.GeneralLinearGroup.ext fun i j => rfl

@[expose] noncomputable def slEquivGL :
    Matrix.SpecialLinearGroup (Fin 5) (ZMod 2) ≃* G :=
  MulEquiv.ofBijective Matrix.SpecialLinearGroup.toGL
    ⟨Matrix.SpecialLinearGroup.toGL_injective, toGL_surjective⟩

theorem slEquivGL_coe (x : Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) :
    ((slEquivGL x : G) : Matrix (Fin 5) (Fin 5) (ZMod 2)) = x := rfl

theorem slEquivGL_stGen (s : Sym) :
    slEquivGL (CFSG.LieType.Steinberg.SL.stGen (m := 4) s) = xg s := by
  obtain ⟨i, j, c⟩ := s
  apply Units.ext
  rw [slEquivGL_coe]
  change _ = symMat (i, j, c)
  by_cases hij : i = j
  · subst hij
    rw [CFSG.LieType.Steinberg.SL.stGen_self, symMat, ite_eq_left (by rfl)]
    rfl
  · rw [CFSG.LieType.Steinberg.SL.stGen_of_ne hij, Matrix.SpecialLinearGroup.transvection_coe,
      symMat, ite_eq_right hij]
    rfl

@[expose] noncomputable def stEquiv :
    PresentedGroup (CFSG.Open.steinbergSLRels 5 (ZMod 2)) ≃* G :=
  (MulEquiv.ofBijective _ (CFSG.LieType.Steinberg.SL.stHom_bijective (m := 4) (F := ZMod 2)
    (by norm_num))).trans slEquivGL

theorem stEquiv_of (s : Sym) : stEquiv (PresentedGroup.of s) = xg s := by
  change slEquivGL (CFSG.LieType.Steinberg.SL.stHom (m := 4) (PresentedGroup.of s)) = xg s
  rw [CFSG.LieType.Steinberg.SL.stHom_of, slEquivGL_stGen]

theorem closure_range_xg : Subgroup.closure (Set.range xg) = ⊤ := by
  have h := MonoidHom.map_closure stEquiv.toMonoidHom (Set.range PresentedGroup.of)
  rw [PresentedGroup.closure_range_of, Subgroup.map_top_of_surjective _ stEquiv.surjective,
    ← Set.range_comp] at h
  have hr : Set.range (stEquiv.toMonoidHom ∘ PresentedGroup.of) = Set.range xg := by
    ext g
    simp only [Set.mem_range, Function.comp_apply, MulEquiv.coe_toMonoidHom, stEquiv_of]
  rw [hr] at h
  exact h.symm


abbrev V := Fin 5 → ZMod 2

@[expose] noncomputable def ρV : G →* (V ≃ₗ[ZMod 2] V) :=
  CFSG.GroupTheory.GLnTwoSplitting.repLinearEquivHom
    (CFSG.GroupTheory.GLnTwoSplitting.naturalRep 5)

theorem ρV_apply (g : G) (v : V) : ρV g v = (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ v := by
  change Matrix.toLin' (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) v = _
  rw [Matrix.toLin'_apply]

abbrev Ω := {f : Fin 5 → ZMod 2 // f ≠ 0}

theorem vecMul_ne_zero (f : Ω) (g : G) :
    f.1 ᵥ* ((g⁻¹ : G) : Matrix (Fin 5) (Fin 5) (ZMod 2)) ≠ 0 := by
  intro h
  apply f.2
  have := congrArg (fun w => w ᵥ* (g : Matrix (Fin 5) (Fin 5) (ZMod 2))) h
  simp only [Matrix.vecMul_vecMul, Matrix.zero_vecMul] at this
  rwa [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.vecMul_one] at this

instance : MulAction G Ω where
  smul g f := ⟨f.1 ᵥ* ((g⁻¹ : G) : Matrix (Fin 5) (Fin 5) (ZMod 2)), vecMul_ne_zero f g⟩
  one_smul f := Subtype.ext (by
    change f.1 ᵥ* ((1⁻¹ : G) : Matrix (Fin 5) (Fin 5) (ZMod 2)) = f.1
    rw [inv_one, Units.val_one, Matrix.vecMul_one])
  mul_smul g h f := Subtype.ext (by
    change f.1 ᵥ* (((g * h)⁻¹ : G) : Matrix (Fin 5) (Fin 5) (ZMod 2)) =
      (f.1 ᵥ* ((h⁻¹ : G) : Matrix (Fin 5) (Fin 5) (ZMod 2))) ᵥ*
        ((g⁻¹ : G) : Matrix (Fin 5) (Fin 5) (ZMod 2))
    rw [Matrix.vecMul_vecMul, _root_.mul_inv_rev, Units.val_mul])


@[expose] def formOf (j : Fin 31) : Fin 5 → ZMod 2 :=
  fun b => if (j.1 + 1).testBit b.1 then 1 else 0

@[expose] def codeOf (f : Fin 5 → ZMod 2) : ℕ := ∑ b : Fin 5, (f b).val * 2 ^ b.1

theorem formOf_ne_zero : ∀ j : Fin 31, formOf j ≠ 0 := by decide

theorem codeOf_lt : ∀ f : Fin 5 → ZMod 2, f ≠ 0 → codeOf f - 1 < 31 := by decide

theorem formOf_codeOf : ∀ (f : Fin 5 → ZMod 2) (hf : f ≠ 0),
    formOf ⟨codeOf f - 1, codeOf_lt f hf⟩ = f := by decide

theorem codeOf_formOf : ∀ j : Fin 31, codeOf (formOf j) - 1 = j.1 := by decide

@[expose] def idxEquiv : Fin 31 ≃ Ω where
  toFun j := ⟨formOf j, formOf_ne_zero j⟩
  invFun f := ⟨codeOf f.1 - 1, codeOf_lt f.1 f.2⟩
  left_inv j := Fin.ext (codeOf_formOf j)
  right_inv f := Subtype.ext (formOf_codeOf f.1 f.2)

instance : MulAction G (Fin 31) := Equiv.mulAction G idxEquiv


theorem zmod2_cases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide


@[expose] def compA (a b : Array (Fin 31)) : Array (Fin 31) :=
  Array.ofFn fun j : Fin 31 => a.getD (b.getD j.1 0).1 0


end CFSG.LocalAnalysis.DempwolffFive
