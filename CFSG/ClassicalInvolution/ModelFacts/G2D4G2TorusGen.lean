module

public import CFSG.ClassicalInvolution.ModelFacts.G2D4SL2Torus
public import CFSG.ClassicalInvolution.ModelFacts.G2D4G2Gen

public noncomputable section

namespace CFSG.ClassicalInvolution.G2D4Models

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ClassicalInvolution.Balance.Bootstrap Matrix
open scoped MatrixGroups

section Torus

variable {τ : Tag} {K : Type} [Field K]

theorem rootDiagUnit_conj_rootChart (w : WeylGroup τ) (i : Fin τ.rank) (b : Fin τ.rank → Kˣ)
    (A : SL2 K) :
    rootDiagUnit τ b * rootChart τ K w i A * (rootDiagUnit τ b)⁻¹ =
      rootChart τ K w i
        (glConjSL (diagGL (rootChar b (w • (Pi.single i 1 : Fin τ.rank → ℤ)))) A) := by
  obtain ⟨ε, hε, hu⟩ := rootChart_uSL (K := K) w i
  obtain ⟨ε', hε', hv⟩ := rootChart_vSL (K := K) w i
  have hγ : IsRoot τ (w • (Pi.single i 1 : Fin τ.rank → ℤ)) :=
    IsRoot.smul (isRoot_single τ i) w
  refine conj_eq_of_generators (Φ := rootChart τ K w i)
    (glConjSL (diagGL (rootChar b (w • (Pi.single i 1 : Fin τ.rank → ℤ))))) (fun c => ?_)
    (fun c => ?_) A
  · rw [hu, glConjSL_diag_uSL, hu, rootDiagUnit_conj_pinnedX b hγ]
    congr 1
    ring
  · rw [hv, glConjSL_diag_vSL, hv, rootDiagUnit_conj_pinnedX b (IsRoot.neg hγ), rootChar_neg_inv]
    congr 1
    simp only [Units.val_inv_eq_inv_val]
    ring

theorem rootChart_one (i : Fin τ.rank) : rootChart τ K 1 i = simpleRootSL2 τ K i :=
  MonoidHom.ext fun A => by simp [rootChart, canonicalRep_one]

end Torus

section G2Torus

variable {K : Type} [Field K]

theorem g2_rootDiagUnit_mem_torusGroup (b : Fin Tag.G2.rank → Kˣ) :
    rootDiagUnit Tag.G2 b ∈ torusGroup Tag.G2 K := by
  have c00 : Tag.G2.cartan g2i0 g2i0 = 2 := by decide
  have c01 : Tag.G2.cartan g2i0 g2i1 = -1 := by decide
  have c10 : Tag.G2.cartan g2i1 g2i0 = -3 := by decide
  have c11 : Tag.G2.cartan g2i1 g2i1 = 2 := by decide
  have h : rootDiagUnit Tag.G2 b = torusElt Tag.G2 K g2i0 (b g2i0 ^ 2 * b g2i1 ^ 3) *
      torusElt Tag.G2 K g2i1 (b g2i0 * b g2i1 ^ 2) := by
    rw [torusElt_eq_rootDiagUnit, torusElt_eq_rootDiagUnit, ← rootDiagUnit_mul]
    congr 1
    funext j
    fin_cases j
    · show b g2i0 = (b g2i0 ^ 2 * b g2i1 ^ 3) ^ Tag.G2.cartan g2i0 g2i0 *
        (b g2i0 * b g2i1 ^ 2) ^ Tag.G2.cartan g2i1 g2i0
      rw [c00, c10]
      apply Units.ext
      simp only [Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_pow_eq_pow_val]
      have := (b g2i0).ne_zero
      have := (b g2i1).ne_zero
      field_simp
    · show b g2i1 = (b g2i0 ^ 2 * b g2i1 ^ 3) ^ Tag.G2.cartan g2i0 g2i1 *
        (b g2i0 * b g2i1 ^ 2) ^ Tag.G2.cartan g2i1 g2i1
      rw [c01, c11]
      apply Units.ext
      simp only [Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_pow_eq_pow_val]
      have := (b g2i0).ne_zero
      have := (b g2i1).ne_zero
      field_simp
  rw [h]
  exact mul_mem (torusElt_mem_torusGroup _ _) (torusElt_mem_torusGroup _ _)

end G2Torus

section Diag

variable {F : Type} [Field F]

theorem exists_unit_sq_ne_one_fin [Finite F] (h4 : 4 ≤ Nat.card F) : ∃ t : Fˣ, t ^ 2 ≠ 1 := by
  let f : Polynomial F := Polynomial.X * (Polynomial.X ^ 2 - 1)
  have hf : f ≠ 0 := by
    intro h
    have := congrArg (fun p => p.coeff 3) h
    simp [f, Polynomial.coeff_X_mul, Polynomial.coeff_X_pow, Polynomial.coeff_one] at this
  have hdeg : f.natDegree < Nat.card F := by
    have : f.natDegree ≤ 3 := by simp only [f]; compute_degree
    omega
  obtain ⟨m, hm⟩ := exists_eval_ne_zero_fin f hf hdeg
  have hm' : m * (m ^ 2 - 1) ≠ 0 := by simpa [f] using hm
  refine ⟨Units.mk0 m (left_ne_zero_of_mul hm'), fun h => ?_⟩
  have := congrArg Units.val h
  simp only [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one] at this
  exact (right_ne_zero_of_mul hm') (by rw [this]; ring)

theorem coe_diagGL_two (s : Fˣ) : ((diagGL s : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
    !![(s : F), 0; 0, 1] := rfl

theorem coe_diagGL_inv_two (s : Fˣ) :
    (((diagGL s)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      !![((s⁻¹ : Fˣ) : F), 0; 0, 1] := rfl

theorem glConjSL_diagGL_apply (s : Fˣ) (A : SL2 F) :
    ((glConjSL (diagGL s) A : SL2 F) : Matrix (Fin 2) (Fin 2) F) =
      !![(A : Matrix (Fin 2) (Fin 2) F) 0 0, (s : F) * (A : Matrix (Fin 2) (Fin 2) F) 0 1;
        ((s⁻¹ : Fˣ) : F) * (A : Matrix (Fin 2) (Fin 2) F) 1 0,
        (A : Matrix (Fin 2) (Fin 2) F) 1 1] := by
  rw [glConjSL_coe, coe_diagGL_two, coe_diagGL_inv_two,
    Matrix.eta_fin_two (A : Matrix (Fin 2) (Fin 2) F)]
  simp only [Matrix.mul_fin_two]
  have hs : (s : F) ≠ 0 := s.ne_zero
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> field_simp

theorem glConjSL_diagGL_apply_00 (s : Fˣ) (A : SL2 F) :
    ((glConjSL (diagGL s) A : SL2 F) : Matrix (Fin 2) (Fin 2) F) 0 0 =
      (A : Matrix (Fin 2) (Fin 2) F) 0 0 := by
  have := congrFun (congrFun (glConjSL_diagGL_apply s A) 0) 0
  simpa using this

theorem glConjSL_diagGL_apply_01 (s : Fˣ) (A : SL2 F) :
    ((glConjSL (diagGL s) A : SL2 F) : Matrix (Fin 2) (Fin 2) F) 0 1 =
      (s : F) * (A : Matrix (Fin 2) (Fin 2) F) 0 1 := by
  have := congrFun (congrFun (glConjSL_diagGL_apply s A) 0) 1
  simpa using this

theorem glConjSL_diagGL_apply_10 (s : Fˣ) (A : SL2 F) :
    ((glConjSL (diagGL s) A : SL2 F) : Matrix (Fin 2) (Fin 2) F) 1 0 =
      ((s⁻¹ : Fˣ) : F) * (A : Matrix (Fin 2) (Fin 2) F) 1 0 := by
  have := congrFun (congrFun (glConjSL_diagGL_apply s A) 1) 0
  simpa using this

theorem glConjSL_diagGL_apply_11 (s : Fˣ) (A : SL2 F) :
    ((glConjSL (diagGL s) A : SL2 F) : Matrix (Fin 2) (Fin 2) F) 1 1 =
      (A : Matrix (Fin 2) (Fin 2) F) 1 1 := by
  have := congrFun (congrFun (glConjSL_diagGL_apply s A) 1) 1
  simpa using this

end Diag

section Gen

variable {F : Type} [Field F] [Finite F]

theorem chart_matrix_antidiag (hodd : Odd (Nat.card F)) (h4 : 4 ≤ Nat.card F)
    {y : ModGL Tag.G2 F} {D : GL (Fin 2) F}
    (hD : ∀ A : SL2 F, y * rootChart Tag.G2 F 1 g2i0 A * y⁻¹ =
      rootChart Tag.G2 F 1 g2i0 (glConjSL D A))
    (hinv : ∀ t ∈ torusGroup Tag.G2 F, y * t * y⁻¹ = t⁻¹) :
    (D : Matrix (Fin 2) (Fin 2) F) 0 0 = 0 ∧ (D : Matrix (Fin 2) (Fin 2) F) 1 1 = 0 := by
  have hK2 : ringChar F ≠ 2 := ringChar_ne_two_of_odd_nat_card hodd
  obtain ⟨t, ht⟩ := exists_unit_sq_ne_one_fin h4
  have hΦinj : Function.Injective (rootChart Tag.G2 F 1 g2i0) := rootChart_injective hK2 1 g2i0
  have hmem : rootChart Tag.G2 F 1 g2i0 (HSL t) ∈ torusGroup Tag.G2 F := by
    rw [rootChart_one, simpleRootSL2_HSL]
    exact torusElt_mem_torusGroup _ _
  have h1 := hinv _ hmem
  rw [hD, ← map_inv] at h1
  have h2 := hΦinj h1
  have h3 := congrArg (fun A : SL2 F => (A : Matrix (Fin 2) (Fin 2) F)) h2
  simp only [glConjSL_coe] at h3
  have h4' : (D : Matrix (Fin 2) (Fin 2) F) * (HSL t : Matrix (Fin 2) (Fin 2) F) =
      (((HSL t)⁻¹ : SL2 F) : Matrix (Fin 2) (Fin 2) F) * (D : Matrix (Fin 2) (Fin 2) F) := by
    rw [← h3, Matrix.mul_assoc, Matrix.mul_assoc, gl_inv_mul D, Matrix.mul_one]
  have e00 := congrFun (congrFun h4' 0) 0
  have e11 := congrFun (congrFun h4' 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two, coe_HSL, Matrix.SpecialLinearGroup.coe_inv,
    Matrix.adjugate_fin_two] at e00 e11
  have htne : (t : F) - (t : F)⁻¹ ≠ 0 := by
    intro h
    apply ht
    apply Units.ext
    have ht0 : (t : F) ≠ 0 := t.ne_zero
    field_simp at h
    simp only [Units.val_pow_eq_pow_val, Units.val_one]
    linear_combination h
  refine ⟨?_, ?_⟩
  · have : (D : Matrix (Fin 2) (Fin 2) F) 0 0 * ((t : F) - (t : F)⁻¹) = 0 := by
      linear_combination e00
    exact (mul_eq_zero.mp this).resolve_right htne
  · have : (D : Matrix (Fin 2) (Fin 2) F) 1 1 * ((t : F) - (t : F)⁻¹) = 0 := by
      linear_combination -e11
    exact (mul_eq_zero.mp this).resolve_right htne


end Gen

section Model

variable {F : Type} [Field F] [Finite F]

omit [Finite F] in
theorem map_centralizer_g2_eq_inf (y : ↥(adjointGroup Tag.G2 F)) :
    (Subgroup.centralizer ({y} : Set ↥(adjointGroup Tag.G2 F))).map
        (adjointGroup Tag.G2 F).subtype =
      adjointGroup Tag.G2 F ⊓
        Subgroup.centralizer ({(y : ModGL Tag.G2 F)} : Set (ModGL Tag.G2 F)) := by
  ext z
  rw [Subgroup.mem_map, Subgroup.mem_inf]
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x.2, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
    exact congrArg Subtype.val hx
  · rintro ⟨hz, hc⟩
    refine ⟨⟨z, hz⟩, ?_, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hc ⊢
    exact Subtype.ext hc


end Model

end CFSG.ClassicalInvolution.G2D4Models
