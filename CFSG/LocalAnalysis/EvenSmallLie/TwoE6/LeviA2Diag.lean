module

public import CFSG.LocalAnalysis.EvenSmallLie.TwoE6.LeviA2DiagEmbed
import all CFSG.Fischer.F4

public noncomputable section

namespace CFSG.EvenSmallLie.TwoE6

open Subgroup
open CFSG.Blueprint.Chevalley CFSG.LieType CFSG.LieType.Steinberg CFSG.LieType.Steinberg.TwistedE6
  CFSG.LieType.Steinberg.Exceptional CFSG.Timmesfeld CFSG.Timmesfeld.LieEmbed
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Std
  CFSG.LieType.Chevalley.C2E6Overlap CFSG.LieType.Steinberg.Isogeny

local notation "𝔽" => GaloisField 2 (2 * 1)

abbrev shortOrbitA : Fin TwistTag.E6.foldedTag.rank := ⟨0, by decide⟩

abbrev shortOrbitB : Fin TwistTag.E6.foldedTag.rank := ⟨1, by decide⟩

theorem mem_orbitField_of_card_two {a : Fin TwistTag.E6.foldedTag.rank}
    (ha : (TwistTag.E6.orbit a).card = 2) (c : K) : c ∈ orbitField TwistTag.E6 K barHom a := by
  rw [mem_orbitField, ha, pow_two, RingHom.coe_mul, Function.comp_apply]
  exact bar_bar c

theorem mem_orbitField_shortOrbitA (c : K) : c ∈ orbitField TwistTag.E6 K barHom shortOrbitA :=
  mem_orbitField_of_card_two (by decide) c

theorem mem_orbitField_shortOrbitB (c : K) : c ∈ orbitField TwistTag.E6 K barHom shortOrbitB :=
  mem_orbitField_of_card_two (by decide) c

abbrev e6t (i : Fin 6) : Fin TwistTag.E6.tag.rank := i

theorem coe_orbitXY_shortOrbit (c : K) :
    (orbitX TwistTag.E6 K barHom shortOrbitA ⟨c, mem_orbitField_shortOrbitA c⟩ :
        ModGL TwistTag.E6.tag K) =
        xUnit TwistTag.E6.tag K (e6t 0) c * xUnit TwistTag.E6.tag K (e6t 5) (barHom c) ∧
      (orbitY TwistTag.E6 K barHom shortOrbitA ⟨c, mem_orbitField_shortOrbitA c⟩ :
        ModGL TwistTag.E6.tag K) =
        yUnit TwistTag.E6.tag K (e6t 0) c * yUnit TwistTag.E6.tag K (e6t 5) (barHom c) ∧
      (orbitX TwistTag.E6 K barHom shortOrbitB ⟨c, mem_orbitField_shortOrbitB c⟩ :
        ModGL TwistTag.E6.tag K) =
        xUnit TwistTag.E6.tag K (e6t 2) c * xUnit TwistTag.E6.tag K (e6t 4) (barHom c) ∧
      (orbitY TwistTag.E6 K barHom shortOrbitB ⟨c, mem_orbitField_shortOrbitB c⟩ :
        ModGL TwistTag.E6.tag K) =
        yUnit TwistTag.E6.tag K (e6t 2) c * yUnit TwistTag.E6.tag K (e6t 4) (barHom c) := by
  have hA : (TwistTag.E6.orbit shortOrbitA).card = 2 := by decide
  have hB : (TwistTag.E6.orbit shortOrbitB).card = 2 := by decide
  have mA : TwistTag.E6.orbitMin shortOrbitA = e6t 0 := by decide
  have mB : TwistTag.E6.orbitMin shortOrbitB = e6t 2 := by decide
  have pA : TwistTag.E6.perm (e6t 0) = e6t 5 := by decide
  have pB : TwistTag.E6.perm (e6t 2) = e6t 4 := by decide
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [coe_orbitX, hA, List.range_succ, List.range_succ, List.range_zero]
    simp only [List.nil_append, List.cons_append, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one, pow_zero, pow_one, mA, pA,
      Equiv.Perm.one_apply, RingHom.coe_one, id_eq]
  · rw [coe_orbitY, hA, List.range_succ, List.range_succ, List.range_zero]
    simp only [List.nil_append, List.cons_append, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one, pow_zero, pow_one, mA, pA,
      Equiv.Perm.one_apply, RingHom.coe_one, id_eq]
  · rw [coe_orbitX, hB, List.range_succ, List.range_succ, List.range_zero]
    simp only [List.nil_append, List.cons_append, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one, pow_zero, pow_one, mB, pB,
      Equiv.Perm.one_apply, RingHom.coe_one, id_eq]
  · rw [coe_orbitY, hB, List.range_succ, List.range_succ, List.range_zero]
    simp only [List.nil_append, List.cons_append, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one, pow_zero, pow_one, mB, pB,
      Equiv.Perm.one_apply, RingHom.coe_one, id_eq]

theorem adjointStd_xm_single
    (i : Fin (Tag.rank .E6)) (c : 𝔽) :
    adjointStd (e6Data_valid.xm 𝔽 (Pi.single i 1) c) = xUnit Tag.E6 K i (fieldEquiv c) := by
  rw [adjointStd_apply, e6Isogeny_xm_single, eltElement_simpleRoot_E6]
  exact baseChangeGL_xUnit _ i c

theorem adjointStd_xm_neg_single
    (i : Fin (Tag.rank .E6)) (c : 𝔽) :
    adjointStd (e6Data_valid.xm 𝔽 (-Pi.single i 1) c) = yUnit Tag.E6 K i (fieldEquiv c) := by
  rw [adjointStd_apply, e6Isogeny_xm_neg_single, eltElement_neg_simpleRoot_E6]
  exact baseChangeGL_yUnit _ i c

theorem fieldEquiv_frobQ
    (c : 𝔽) : fieldEquiv (frobQ 2 1 c) = barHom (fieldEquiv c) :=
  (barHom_fieldEquiv c).symm

theorem coe_isogenyStd_levi34Hom_tv01
    (c : 𝔽) :
    (isogenyStd (levi34Hom (tv 0 1 c)) : ModGL Tag.E6 K) =
      xUnit Tag.E6 K (e6n 0) (fieldEquiv c) * xUnit Tag.E6 K (e6n 5) (barHom (fieldEquiv c)) := by
  rw [coe_isogenyStd_eq_adjointStd, levi34Hom_tv01, map_mul, adjointStd_xm_single,
    adjointStd_xm_single, fieldEquiv_frobQ]

theorem coe_isogenyStd_levi34Hom_tv10
    (c : 𝔽) :
    (isogenyStd (levi34Hom (tv 1 0 c)) : ModGL Tag.E6 K) =
      yUnit Tag.E6 K (e6n 0) (fieldEquiv c) * yUnit Tag.E6 K (e6n 5) (barHom (fieldEquiv c)) := by
  rw [coe_isogenyStd_eq_adjointStd, levi34Hom_tv10, map_mul, adjointStd_xm_neg_single,
    adjointStd_xm_neg_single, fieldEquiv_frobQ]

theorem coe_isogenyStd_levi34Hom_tv12
    (c : 𝔽) :
    (isogenyStd (levi34Hom (tv 1 2 c)) : ModGL Tag.E6 K) =
      xUnit Tag.E6 K (e6n 2) (fieldEquiv c) * xUnit Tag.E6 K (e6n 4) (barHom (fieldEquiv c)) := by
  rw [coe_isogenyStd_eq_adjointStd, levi34Hom_tv12, map_mul, adjointStd_xm_single,
    adjointStd_xm_single, fieldEquiv_frobQ]

theorem coe_isogenyStd_levi34Hom_tv21
    (c : 𝔽) :
    (isogenyStd (levi34Hom (tv 2 1 c)) : ModGL Tag.E6 K) =
      yUnit Tag.E6 K (e6n 2) (fieldEquiv c) * yUnit Tag.E6 K (e6n 4) (barHom (fieldEquiv c)) := by
  rw [coe_isogenyStd_eq_adjointStd, levi34Hom_tv21, map_mul, adjointStd_xm_neg_single,
    adjointStd_xm_neg_single, fieldEquiv_frobQ]

@[expose] def levi34OmegaUnit : (orbitField TwistTag.E6 K barHom shortOrbitA)ˣ :=
  Units.mk0 ⟨ω, mem_orbitField_shortOrbitA ω⟩ fun h => absurd (congrArg Subtype.val h) (by decide)

@[expose] def levi34Unit :
    (a : Fin TwistTag.E6.foldedTag.rank) → (orbitField TwistTag.E6 K barHom a)ˣ :=
  Pi.mulSingle shortOrbitA levi34OmegaUnit

abbrev levi34Diag
    : MulAut stdGroup := compatDiagAutHom TwistTag.E6 K barHom levi34Unit

theorem levi34Unit_shortOrbitA : levi34Unit shortOrbitA = levi34OmegaUnit :=
  Pi.mulSingle_eq_same _ _

theorem levi34Unit_shortOrbitB : levi34Unit shortOrbitB = 1 :=
  Pi.mulSingle_eq_of_ne (by decide) _

theorem coe_levi34Diag_xA
    {g : stdGroup} {c : K}
    (hg : (g : ModGL Tag.E6 K) = xUnit Tag.E6 K (e6n 0) c * xUnit Tag.E6 K (e6n 5) (barHom c)) :
    (levi34Diag g : ModGL Tag.E6 K) =
      xUnit Tag.E6 K (e6n 0) (ω * c) * xUnit Tag.E6 K (e6n 5) (barHom (ω * c)) := by
  have hg' : (g : ModGL Tag.E6 K) = (orbitX TwistTag.E6 K barHom shortOrbitA
      ⟨c, mem_orbitField_shortOrbitA c⟩ : ModGL TwistTag.E6.tag K) :=
    hg.trans (coe_orbitXY_shortOrbit c).1.symm
  have hu : ((levi34Unit shortOrbitA : (orbitField TwistTag.E6 K barHom shortOrbitA)ˣ) :
      orbitField TwistTag.E6 K barHom shortOrbitA) * ⟨c, mem_orbitField_shortOrbitA c⟩ =
        ⟨ω * c, mem_orbitField_shortOrbitA _⟩ := by
    rw [levi34Unit_shortOrbitA]
    rfl
  refine (coe_compatDiagAutHom levi34Unit g).trans ?_
  refine Eq.trans ?_ (coe_orbitXY_shortOrbit (ω * c)).1
  rw [← hu, ← compatDiag_conj_orbitX levi34Unit shortOrbitA, hg']

theorem coe_levi34Diag_yA
    {g : stdGroup} {c : K}
    (hg : (g : ModGL Tag.E6 K) = yUnit Tag.E6 K (e6n 0) c * yUnit Tag.E6 K (e6n 5) (barHom c)) :
    (levi34Diag g : ModGL Tag.E6 K) =
      yUnit Tag.E6 K (e6n 0) (ω⁻¹ * c) * yUnit Tag.E6 K (e6n 5) (barHom (ω⁻¹ * c)) := by
  have hg' : (g : ModGL Tag.E6 K) = (orbitY TwistTag.E6 K barHom shortOrbitA
      ⟨c, mem_orbitField_shortOrbitA c⟩ : ModGL TwistTag.E6.tag K) :=
    hg.trans (coe_orbitXY_shortOrbit c).2.1.symm
  have hu : (((levi34Unit shortOrbitA)⁻¹ : (orbitField TwistTag.E6 K barHom shortOrbitA)ˣ) :
      orbitField TwistTag.E6 K barHom shortOrbitA) * ⟨c, mem_orbitField_shortOrbitA c⟩ =
        ⟨ω⁻¹ * c, mem_orbitField_shortOrbitA _⟩ := by
    rw [levi34Unit_shortOrbitA]
    rfl
  refine (coe_compatDiagAutHom levi34Unit g).trans ?_
  refine Eq.trans ?_ (coe_orbitXY_shortOrbit (ω⁻¹ * c)).2.1
  rw [← hu, ← compatDiag_conj_orbitY levi34Unit shortOrbitA, hg']

theorem coe_levi34Diag_xB
    {g : stdGroup} {c : K}
    (hg : (g : ModGL Tag.E6 K) = xUnit Tag.E6 K (e6n 2) c * xUnit Tag.E6 K (e6n 4) (barHom c)) :
    (levi34Diag g : ModGL Tag.E6 K) = g := by
  have hg' : (g : ModGL Tag.E6 K) = (orbitX TwistTag.E6 K barHom shortOrbitB
      ⟨c, mem_orbitField_shortOrbitB c⟩ : ModGL TwistTag.E6.tag K) :=
    hg.trans (coe_orbitXY_shortOrbit c).2.2.1.symm
  have hu : ((levi34Unit shortOrbitB : (orbitField TwistTag.E6 K barHom shortOrbitB)ˣ) :
      orbitField TwistTag.E6 K barHom shortOrbitB) * ⟨c, mem_orbitField_shortOrbitB c⟩ =
        ⟨c, mem_orbitField_shortOrbitB _⟩ := by
    rw [levi34Unit_shortOrbitB, Units.val_one, one_mul]
  refine (coe_compatDiagAutHom levi34Unit g).trans ?_
  rw [hg', compatDiag_conj_orbitX levi34Unit shortOrbitB, hu]

theorem coe_levi34Diag_yB
    {g : stdGroup} {c : K}
    (hg : (g : ModGL Tag.E6 K) = yUnit Tag.E6 K (e6n 2) c * yUnit Tag.E6 K (e6n 4) (barHom c)) :
    (levi34Diag g : ModGL Tag.E6 K) = g := by
  have hg' : (g : ModGL Tag.E6 K) = (orbitY TwistTag.E6 K barHom shortOrbitB
      ⟨c, mem_orbitField_shortOrbitB c⟩ : ModGL TwistTag.E6.tag K) :=
    hg.trans (coe_orbitXY_shortOrbit c).2.2.2.symm
  have hu : (((levi34Unit shortOrbitB)⁻¹ : (orbitField TwistTag.E6 K barHom shortOrbitB)ˣ) :
      orbitField TwistTag.E6 K barHom shortOrbitB) * ⟨c, mem_orbitField_shortOrbitB c⟩ =
        ⟨c, mem_orbitField_shortOrbitB _⟩ := by
    rw [levi34Unit_shortOrbitB, inv_one, Units.val_one, one_mul]
  refine (coe_compatDiagAutHom levi34Unit g).trans ?_
  rw [hg', compatDiag_conj_orbitY levi34Unit shortOrbitB, hu]

theorem levi34Diag_pow_three :
    levi34Diag ^ 3 = 1 := by
  have hω : levi34OmegaUnit ^ 3 = 1 := Units.ext (Subtype.ext (by
    rw [Units.val_pow_eq_pow_val, SubmonoidClass.coe_pow]
    decide))
  have hu : levi34Unit ^ 3 = 1 := by
    rw [levi34Unit, ← Pi.mulSingle_pow, hω, Pi.mulSingle_one]
  have h := (map_pow (compatDiagAutHom TwistTag.E6 K barHom) levi34Unit 3).symm
  rw [hu, map_one] at h
  exact h

theorem omegaK_ne_zero : ω ≠ 0 := by decide

theorem natCard_K : Nat.card K = 4 := by
  rw [Nat.card_eq_fintype_card, card_K]

@[expose] def diagOmegaGL : GL (Fin 3) K where
  val := !![ω, 0, 0; 0, 1, 0; 0, 0, 1]
  inv := !![ω⁻¹, 0, 0; 0, 1, 0; 0, 0, 1]
  val_inv := by
    rw [Matrix.mul_fin_three]
    simp [mul_inv_cancel₀ omegaK_ne_zero, Matrix.one_fin_three]
  inv_val := by
    rw [Matrix.mul_fin_three]
    simp [inv_mul_cancel₀ omegaK_ne_zero, Matrix.one_fin_three]

theorem coe_diagOmegaGL :
    (diagOmegaGL : Matrix (Fin 3) (Fin 3) K) = !![ω, 0, 0; 0, 1, 0; 0, 0, 1] :=
  rfl

theorem coe_diagOmegaGL_inv :
    ((diagOmegaGL⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      !![ω⁻¹, 0, 0; 0, 1, 0; 0, 0, 1] :=
  rfl

theorem det_diagOmegaGL : (diagOmegaGL : Matrix (Fin 3) (Fin 3) K).det = ω := by
  rw [coe_diagOmegaGL, Matrix.det_fin_three]
  simp

theorem det_diagOmegaGL_ne_one : (diagOmegaGL : Matrix (Fin 3) (Fin 3) K).det ≠ 1 := by
  rw [det_diagOmegaGL]
  decide


@[expose] def conjSL3 (g : GL (Fin 3) K) :
    Matrix.SpecialLinearGroup (Fin 3) K →* Matrix.SpecialLinearGroup (Fin 3) K where
  toFun A := ⟨(g : Matrix (Fin 3) (Fin 3) K) * (A : Matrix (Fin 3) (Fin 3) K) *
      ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K), by
    rw [Matrix.det_mul, Matrix.det_mul, A.2, mul_one, ← Matrix.det_mul, ← Units.val_mul,
      mul_inv_cancel, Units.val_one, Matrix.det_one]⟩
  map_one' := Subtype.ext <| by
    change (g : Matrix (Fin 3) (Fin 3) K) * 1 *
      ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1
    rw [Matrix.mul_one, Units.mul_inv]
  map_mul' A B := Subtype.ext <| by
    change (g : Matrix (Fin 3) (Fin 3) K) *
        ((A : Matrix (Fin 3) (Fin 3) K) * (B : Matrix (Fin 3) (Fin 3) K)) *
          ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((g : Matrix (Fin 3) (Fin 3) K) * (A : Matrix (Fin 3) (Fin 3) K) *
          ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) *
        ((g : Matrix (Fin 3) (Fin 3) K) * (B : Matrix (Fin 3) (Fin 3) K) *
          ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))
    simp only [Matrix.mul_assoc, Units.inv_mul_cancel_left]

theorem coe_conjSL3 (g : GL (Fin 3) K) (A : Matrix.SpecialLinearGroup (Fin 3) K) :
    ((conjSL3 g A : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (g : Matrix (Fin 3) (Fin 3) K) * (A : Matrix (Fin 3) (Fin 3) K) *
        ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) :=
  rfl

theorem conjSL3_diagOmegaGL_tv (c : K) :
    conjSL3 diagOmegaGL (tv 0 1 c) = tv 0 1 (ω * c) ∧
      conjSL3 diagOmegaGL (tv 1 0 c) = tv 1 0 (ω⁻¹ * c) ∧
      conjSL3 diagOmegaGL (tv 1 2 c) = tv 1 2 c ∧ conjSL3 diagOmegaGL (tv 2 1 c) = tv 2 1 c := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply Matrix.SpecialLinearGroup.coeMonoidHom_injective <;>
    rw [Matrix.SpecialLinearGroup.coeMonoidHom_apply, coe_conjSL3, coe_diagOmegaGL,
      coe_diagOmegaGL_inv]
  · rw [← Matrix.SpecialLinearGroup.coeMonoidHom_apply (tv 0 1 c), LevisExtras.cm_tv01,
      LevisExtras.cm_tv01, Matrix.mul_fin_three, Matrix.mul_fin_three]
    simp [mul_inv_cancel₀ omegaK_ne_zero, mul_comm]
  · rw [← Matrix.SpecialLinearGroup.coeMonoidHom_apply (tv 1 0 c), LevisExtras.cm_tv10,
      LevisExtras.cm_tv10, Matrix.mul_fin_three, Matrix.mul_fin_three]
    simp [mul_inv_cancel₀ omegaK_ne_zero, mul_comm]
  · rw [← Matrix.SpecialLinearGroup.coeMonoidHom_apply (tv 1 2 c), LevisExtras.cm_tv12,
      Matrix.mul_fin_three, Matrix.mul_fin_three]
    simp [mul_inv_cancel₀ omegaK_ne_zero]
  · rw [← Matrix.SpecialLinearGroup.coeMonoidHom_apply (tv 2 1 c), LevisExtras.cm_tv21,
      Matrix.mul_fin_three, Matrix.mul_fin_three]
    simp [mul_inv_cancel₀ omegaK_ne_zero]

abbrev slFieldEquivSymm :
    Matrix.SpecialLinearGroup (Fin 3) K →* Matrix.SpecialLinearGroup (Fin 3) 𝔽 :=
  Matrix.SpecialLinearGroup.map fieldEquiv.symm.toRingHom

theorem slFieldEquivSymm_surjective : Function.Surjective slFieldEquivSymm := fun A =>
  ⟨Matrix.SpecialLinearGroup.map fieldEquiv.toRingHom A, Matrix.SpecialLinearGroup.ext _ _
    fun i j => by simp⟩

@[expose] def levi34HomK
    : Matrix.SpecialLinearGroup (Fin 3) K →* twistedE6Group 2 1 :=
  levi34Hom.comp slFieldEquivSymm

theorem levi34HomK_tv
    (i j : Fin 3) (c : K) :
    levi34HomK (tv i j c) = levi34Hom (tv i j (fieldEquiv.symm c)) := by
  rw [levi34HomK, MonoidHom.comp_apply, map_tv]
  rfl

theorem levi34HomK_injective
    : Function.Injective levi34HomK :=
  levi34Hom_injective.comp map_sl_injective

theorem range_levi34HomK
    : levi34HomK.range = (twistedE6Datum 2 1).levi levi34 := by
  rw [levi34HomK, MonoidHom.range_comp, MonoidHom.range_eq_top.2 slFieldEquivSymm_surjective,
    Subgroup.map_top, range_levi34Hom]

@[expose] def levi34Equiv :
    (twistedE6Datum 2 1).levi levi34 ≃* Matrix.SpecialLinearGroup (Fin 3) K :=
  ((MonoidHom.ofInjective levi34HomK_injective).trans
    (MulEquiv.subgroupCongr range_levi34HomK)).symm


theorem levi34Diag_comp_isogenyStd :
    (levi34Diag.toMonoidHom.comp (isogenyStd.comp levi34HomK)) =
      (isogenyStd.comp levi34HomK).comp (conjSL3 diagOmegaGL) := by
  refine sl3_hom_ext (fun c => Subtype.ext ?_) (fun c => Subtype.ext ?_)
    (fun c => Subtype.ext ?_) (fun c => Subtype.ext ?_)
  · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, (conjSL3_diagOmegaGL_tv c).1,
      levi34HomK_tv]
    rw [coe_isogenyStd_levi34Hom_tv01, fieldEquiv.apply_symm_apply]
    exact coe_levi34Diag_xA (by rw [coe_isogenyStd_levi34Hom_tv01, fieldEquiv.apply_symm_apply])
  · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, (conjSL3_diagOmegaGL_tv c).2.1,
      levi34HomK_tv]
    rw [coe_isogenyStd_levi34Hom_tv10, fieldEquiv.apply_symm_apply]
    exact coe_levi34Diag_yA (by rw [coe_isogenyStd_levi34Hom_tv10, fieldEquiv.apply_symm_apply])
  · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, (conjSL3_diagOmegaGL_tv c).2.2.1]
    exact coe_levi34Diag_xB (by rw [levi34HomK_tv, coe_isogenyStd_levi34Hom_tv12,
      fieldEquiv.apply_symm_apply])
  · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, (conjSL3_diagOmegaGL_tv c).2.2.2]
    exact coe_levi34Diag_yB (by rw [levi34HomK_tv, coe_isogenyStd_levi34Hom_tv21,
      fieldEquiv.apply_symm_apply])


end CFSG.EvenSmallLie.TwoE6
