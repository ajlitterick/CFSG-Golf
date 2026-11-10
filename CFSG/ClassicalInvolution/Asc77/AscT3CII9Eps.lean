module

public import CFSG.ClassicalInvolution.Asc77.AscT3CIIOut

public section

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open CFSG.RankThree.PartTwo.KFacts CFSG.GorensteinWalter
  CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open scoped MatrixGroups commutatorElement

section Diag

variable (K : Type*) [Field K]

abbrev pslRange : Subgroup (PGL2 K) :=
  (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range

theorem ofAdd_one_mul_self :
    (Multiplicative.ofAdd (1 : ZMod 2)) * Multiplicative.ofAdd 1 = 1 := by decide

open Classical in
@[expose] noncomputable def diagHom [Finite K] (hK : IsOddPrimePower (Nat.card K)) :
    PGL2 K →* Multiplicative (ZMod 2) where
  toFun g := if g ∈ pslRange K then 1 else Multiplicative.ofAdd 1
  map_one' := by simp
  map_mul' g h := by
    have hH := pgl2_psl2Range_index_eq_two K hK
    have key := (Subgroup.mul_mem_iff_of_index_two hH (a := g) (b := h))
    by_cases hg : g ∈ pslRange K <;> by_cases hh : h ∈ pslRange K
    · have : g * h ∈ pslRange K := (Subgroup.mul_mem _ hg hh)
      simp [hg, hh, this]
    · have : g * h ∉ pslRange K := fun hc => by
        have := key.mp hc
        exact hh (this.mp hg)
      simp [hg, hh, this]
    · have : g * h ∉ pslRange K := fun hc => by
        have := key.mp hc
        exact hg (this.mpr hh)
      simp [hg, hh, this]
    · have : g * h ∈ pslRange K := key.mpr (iff_of_false hg hh)
      simp [hg, hh, this, ofAdd_one_mul_self]

theorem diagHom_eq_one_iff [Finite K] (hK : IsOddPrimePower (Nat.card K)) (g : PGL2 K) :
    diagHom K hK g = 1 ↔ g ∈ pslRange K := by
  unfold diagHom
  simp only [MonoidHom.coe_mk, OneHom.coe_mk]
  by_cases h : g ∈ pslRange K <;> simp [h]

theorem diagHom_fieldAut [Finite K] (hK : IsOddPrimePower (Nat.card K)) (σ : K ≃+* K)
    (g : PGL2 K) : diagHom K hK (pgl2FieldAut K σ g) = diagHom K hK g := by
  unfold diagHom
  simp only [MonoidHom.coe_mk, OneHom.coe_mk]
  by_cases h : g ∈ pslRange K
  · have h2 : pgl2FieldAut K σ g ∈ pslRange K := (pgl2FieldAut_mem_range_iff σ).mpr h
    simp only [h2, h, ↓reduceIte]
  · have h2 : pgl2FieldAut K σ g ∉ pslRange K := fun hc =>
      h ((pgl2FieldAut_mem_range_iff σ).mp hc)
    simp only [h2, h, ↓reduceIte]

@[expose] noncomputable def epsGamma [Finite K] (hK : IsOddPrimePower (Nat.card K)) :
    PGammaL2 K →* Multiplicative (ZMod 2) :=
  SemidirectProduct.lift (diagHom K hK) 1 (fun σ => by
    ext g
    simp [diagHom_fieldAut])

@[expose] noncomputable def psl2Eps [Finite K] (hK : IsOddPrimePower (Nat.card K)) :
    MulAut (PSL2 K) →* Multiplicative (ZMod 2) :=
  (epsGamma K hK).comp (semilinearEquivAut K).symm.toMonoidHom

@[expose] noncomputable def psl2Rho [Finite K] : MulAut (PSL2 K) →* (K ≃+* K) :=
  SemidirectProduct.rightHom.comp (semilinearEquivAut K).symm.toMonoidHom

theorem pglAction_mul_eq [Finite K] (g : PGL2 K) (σ : K ≃+* K) :
    pglAction K g * psl2FieldAut K σ =
      semilinearEquivAut K (SemidirectProduct.inl g * SemidirectProduct.inr σ) := by
  change _ = semilinearAction K _
  rw [map_mul, semilinearAction_inl, semilinearAction_inr]

theorem psl2Eps_pglAction_mul [Finite K] (hK : IsOddPrimePower (Nat.card K)) (g : PGL2 K)
    (σ : K ≃+* K) : psl2Eps K hK (pglAction K g * psl2FieldAut K σ) = diagHom K hK g := by
  rw [pglAction_mul_eq]
  change epsGamma K hK ((semilinearEquivAut K).symm _) = _
  rw [MulEquiv.symm_apply_apply, map_mul]
  simp [epsGamma]

theorem psl2Rho_pglAction_mul [Finite K] (g : PGL2 K) (σ : K ≃+* K) :
    psl2Rho K (pglAction K g * psl2FieldAut K σ) = σ := by
  rw [pglAction_mul_eq]
  change SemidirectProduct.rightHom ((semilinearEquivAut K).symm _) = _
  rw [MulEquiv.symm_apply_apply, map_mul]
  simp

end Diag

section SL

variable (F : Type*) [Field F] [Finite F]

@[expose] noncomputable def slEps (hK : IsOddPrimePower (Nat.card F)) :
    MulAut SL(2, F) →* Multiplicative (ZMod 2) :=
  (psl2Eps F hK).comp (centerDescend SL(2, F))

@[expose] noncomputable def slRho : MulAut SL(2, F) →* (F ≃+* F) :=
  (psl2Rho F).comp (centerDescend SL(2, F))

@[expose] noncomputable def slFieldAut (σ : F ≃+* F) : MulAut SL(2, F) :=
  MonoidHom.toMulEquiv (Matrix.SpecialLinearGroup.map σ.toRingHom)
    (Matrix.SpecialLinearGroup.map σ.symm.toRingHom)
    (by ext x i j; simp) (by ext x i j; simp)

omit [Finite F] in
theorem slFieldAut_apply (σ : F ≃+* F) (x : SL(2, F)) :
    slFieldAut F σ x = Matrix.SpecialLinearGroup.map σ.toRingHom x := rfl

omit [Finite F] in
theorem slFieldAut_entry (σ : F ≃+* F) (x : SL(2, F)) (i j : Fin 2) :
    ((slFieldAut F σ x : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) i j = σ (x i j) := rfl

omit [Finite F] in
theorem centerDescend_slFieldAut (σ : F ≃+* F) :
    centerDescend SL(2, F) (slFieldAut F σ) = psl2FieldAut F σ := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H y =>
    rw [centerDescend_mk, psl2FieldAut_apply]
    exact (psl2RingEquiv_mk σ y).symm

theorem slEps_slFieldAut (hK : IsOddPrimePower (Nat.card F)) (σ : F ≃+* F) :
    slEps F hK (slFieldAut F σ) = 1 := by
  have h := psl2Eps_pglAction_mul F hK (1 : PGL2 F) σ
  rw [map_one, one_mul, map_one] at h
  simpa [slEps, centerDescend_slFieldAut] using h

theorem slRho_slFieldAut (σ : F ≃+* F) : slRho F (slFieldAut F σ) = σ := by
  have h := psl2Rho_pglAction_mul F (1 : PGL2 F) σ
  rw [map_one, one_mul] at h
  simpa [slRho, centerDescend_slFieldAut] using h

theorem slEps_conj (hK : IsOddPrimePower (Nat.card F)) (x : SL(2, F)) :
    slEps F hK (MulAut.conj x) = 1 := by
  have h1 : centerDescend SL(2, F) (MulAut.conj x) = pglAction F
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (QuotientGroup.mk x)) := by
    rw [centerDescend_conj, pglAction_toPGL]
  have h2 := psl2Eps_pglAction_mul F hK
    (Matrix.ProjectiveSpecialLinearGroup.toPGL (QuotientGroup.mk x : PSL2 F)) 1
  rw [map_one, mul_one] at h2
  simp only [slEps, MonoidHom.comp_apply, h1, h2, diagHom_eq_one_iff]
  exact ⟨_, rfl⟩

theorem slRho_conj (x : SL(2, F)) : slRho F (MulAut.conj x) = 1 := by
  have h1 : centerDescend SL(2, F) (MulAut.conj x) = pglAction F
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (QuotientGroup.mk x)) := by
    rw [centerDescend_conj, pglAction_toPGL]
  have h2 := psl2Rho_pglAction_mul F
    (Matrix.ProjectiveSpecialLinearGroup.toPGL (QuotientGroup.mk x : PSL2 F)) 1
  rw [map_one, mul_one] at h2
  simp only [slRho, MonoidHom.comp_apply, h1, h2]

theorem slEps_slRho_eq_one_iff (hK : IsOddPrimePower (Nat.card F)) (h4 : 4 ≤ Nat.card F)
    (α : MulAut SL(2, F)) :
    (slEps F hK α = 1 ∧ slRho F α = 1) ↔ IsInnerAut α := by
  constructor
  · rintro ⟨hε, hρ⟩
    have hperf : Group.IsPerfect SL(2, F) := CFSG.ClassicalInvolution.sl2_isPerfect h4
    refine isInnerAut_of_isInnerAut_centerDescend ?_
    obtain ⟨g, σ, hα⟩ := exists_pglAction_mul_psl2FieldAut (centerDescend SL(2, F) α)
    have h1 : psl2Rho F (centerDescend SL(2, F) α) = σ := by
      rw [hα, psl2Rho_pglAction_mul]
    have h2 : psl2Eps F hK (centerDescend SL(2, F) α) = diagHom F hK g := by
      rw [hα, psl2Eps_pglAction_mul]
    have hσ : σ = 1 := by rw [← h1]; exact hρ
    have hg : g ∈ pslRange F := (diagHom_eq_one_iff F hK g).mp (by rw [← h2]; exact hε)
    obtain ⟨x, rfl⟩ := hg
    refine ⟨x, ?_⟩
    rw [hα, hσ, map_one, mul_one, pglAction_toPGL]
  · rintro ⟨x, rfl⟩
    exact ⟨slEps_conj F hK x, slRho_conj F x⟩

end SL

section OutHoms

variable {F : Type*} [Field F] [Finite F] {P : Type*} [Group P]


theorem ringAut_conj_eq (σ τ : F ≃+* F) : σ * τ * σ⁻¹ = τ := by
  rw [CFSG.LocalAnalysis.ComponentInitial.ringAut_mul_comm F σ τ]
  group


end OutHoms

end CFSG.ClassicalInvolution.Asc77.T3CII
