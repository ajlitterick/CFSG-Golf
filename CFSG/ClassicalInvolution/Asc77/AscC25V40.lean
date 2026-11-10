module

public import CFSG.ClassicalInvolution.Asc77.AscC25V35

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.C25V

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
  CFSG.GorensteinWalter
open scoped MatrixGroups commutatorElement

section Diag

variable {F : Type} [Field F] [Finite F]

theorem exists_toPGL_of_diagPGL_eq_one (h : PGL2 F) (hh : diagPGL h = 1) :
    ∃ y : PSL2 F, h = Matrix.ProjectiveSpecialLinearGroup.toPGL y := by
  classical
  obtain ⟨g, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective h
  have hsq : IsSquare ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) := (sqHom_eq_one_iff _).mp hh
  obtain ⟨μ, hμ⟩ := hsq
  have hμ0 : μ ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hμ
    exact (Matrix.GeneralLinearGroup.det g).ne_zero hμ
  have hdetM : (μ⁻¹ • (g : Matrix (Fin 2) (Fin 2) F)).det = 1 := by
    rw [Matrix.det_smul, Fintype.card_fin]
    have h1 : (g : Matrix (Fin 2) (Fin 2) F).det = μ * μ := by
      have := hμ
      simpa using this
    rw [h1]
    field_simp
  refine ⟨QuotientGroup.mk ⟨μ⁻¹ • (g : Matrix (Fin 2) (Fin 2) F), hdetM⟩, ?_⟩
  show Matrix.ProjGenLinGroup.mk g = Matrix.ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL
    ⟨μ⁻¹ • (g : Matrix (Fin 2) (Fin 2) F), hdetM⟩)
  rw [Matrix.ProjGenLinGroup.mk_eq_mk_iff]
  refine ⟨Units.mk0 μ⁻¹ (inv_ne_zero hμ0), ?_⟩
  apply Units.ext
  have e : ((Matrix.SpecialLinearGroup.toGL
      (⟨μ⁻¹ • (g : Matrix (Fin 2) (Fin 2) F), hdetM⟩ : Matrix.SpecialLinearGroup (Fin 2) F) :
        GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = μ⁻¹ • (g : Matrix (Fin 2) (Fin 2) F) := rfl
  rw [e]
  ext i j
  simp only [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.mul_apply,
    Matrix.smul_apply, smul_eq_mul]
  fin_cases j <;> simp [Matrix.diagonal_apply, mul_comm]

end Diag

section Nu

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

@[expose] noncomputable def nuK (hp : p ≠ 2) (hq : 5 ≤ p ^ f) {K : Subgroup G}
    (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, GaloisField p f)) :
    Subgroup.normalizer (K : Set G) →* PGammaL2 (GaloisField p f) :=
  normalizerToPGammaL2Mod e (gf_facts hp hq).2.1 (gf_facts hp hq).2.2.1 (gf_facts hp hq).2.2.2


@[expose] noncomputable def nuG (hp : p ≠ 2) (hq : 5 ≤ p ^ f) {K : Subgroup G}
    (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, GaloisField p f)) (x : G) :
    PGammaL2 (GaloisField p f) := by
  classical
  exact if hx : x ∈ Subgroup.normalizer (K : Set G) then nuK hp hq e ⟨x, hx⟩ else 1

variable (hp : p ≠ 2) (hq : 5 ≤ p ^ f) {K : Subgroup G}
  (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, GaloisField p f))

include hp hq in
theorem nuG_of_mem {x : G} (hx : x ∈ Subgroup.normalizer (K : Set G)) :
    nuG hp hq e x = nuK hp hq e ⟨x, hx⟩ := by
  simp [nuG, hx]

include hp hq in
theorem nuG_mul {a b : G} (ha : a ∈ Subgroup.normalizer (K : Set G))
    (hb : b ∈ Subgroup.normalizer (K : Set G)) :
    nuG hp hq e (a * b) = nuG hp hq e a * nuG hp hq e b := by
  have hmul : (⟨a * b, Subgroup.mul_mem _ ha hb⟩ : Subgroup.normalizer (K : Set G)) =
      ⟨a, ha⟩ * ⟨b, hb⟩ := rfl
  rw [nuG_of_mem hp hq e ha, nuG_of_mem hp hq e hb,
    nuG_of_mem hp hq e (Subgroup.mul_mem _ ha hb), hmul, map_mul]

include hp hq in
theorem nuG_inv {a : G} (ha : a ∈ Subgroup.normalizer (K : Set G)) :
    nuG hp hq e a⁻¹ = (nuG hp hq e a)⁻¹ := by
  have hinv : (⟨a⁻¹, Subgroup.inv_mem _ ha⟩ : Subgroup.normalizer (K : Set G)) = ⟨a, ha⟩⁻¹ := rfl
  rw [nuG_of_mem hp hq e ha, nuG_of_mem hp hq e (Subgroup.inv_mem _ ha), hinv, map_inv]


include hp hq in
theorem nuG_conj {a b : G} (ha : a ∈ Subgroup.normalizer (K : Set G))
    (hb : b ∈ Subgroup.normalizer (K : Set G)) :
    nuG hp hq e (a * b * a⁻¹) = nuG hp hq e a * nuG hp hq e b * (nuG hp hq e a)⁻¹ := by
  rw [nuG_mul hp hq e (Subgroup.mul_mem _ ha hb) (Subgroup.inv_mem _ ha), nuG_mul hp hq e ha hb,
    nuG_inv hp hq e ha]

include hp hq in
theorem nuG_one : nuG hp hq e (1 : G) = 1 := by
  have hone : (⟨1, Subgroup.one_mem _⟩ : Subgroup.normalizer (K : Set G)) = 1 := rfl
  rw [nuG_of_mem hp hq e (Subgroup.one_mem _), hone, map_one]

include hp hq in
theorem nuG_eq_one_iff {n : G} (hn : n ∈ Subgroup.normalizer (K : Set G)) :
    nuG hp hq e n = 1 ↔ ∀ l ∈ K, ⁅n, l⁆ ∈ oddCoreOf K := by
  rw [nuG_of_mem hp hq e hn]
  exact Hall196.normalizerToPGammaL2Mod_eq_one_iff e (gf_facts hp hq).2.1
    (gf_facts hp hq).2.2.1 (gf_facts hp hq).2.2.2 ⟨n, hn⟩

include hp hq in
theorem fieldChar_eq_rightHom_nuG {n : G} (hn : n ∈ Subgroup.normalizer (K : Set G)) :
    fieldChar hp hq e ⟨n, hn⟩ = SemidirectProduct.rightHom (nuG hp hq e n) := by
  rw [nuG_of_mem hp hq e hn]
  rfl

include hp hq in
theorem diagChar_eq_diagGamma_nuG {n : G} (hn : n ∈ Subgroup.normalizer (K : Set G)) :
    diagChar hp hq e ⟨n, hn⟩ = diagGamma (nuG hp hq e n) := by
  rw [nuG_of_mem hp hq e hn]
  rfl

include hp hq in
theorem exists_mem_K_nuG_eq_inr {n : G} (hn : n ∈ Subgroup.normalizer (K : Set G))
    (hδ : diagChar hp hq e ⟨n, hn⟩ = 1) :
    ∃ k ∈ K, nuG hp hq e (k⁻¹ * n) = SemidirectProduct.inr (fieldChar hp hq e ⟨n, hn⟩) := by
  classical
  let α : PGammaL2 (GaloisField p f) := nuK hp hq e ⟨n, hn⟩
  have hαδ : diagPGL α.left = 1 := by
    rw [← diagGamma_apply]
    exact hδ
  obtain ⟨y, hy⟩ := exists_toPGL_of_diagPGL_eq_one α.left hαδ
  obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective y
  obtain ⟨κ, hκ⟩ := QuotientGroup.mk_surjective (e.symm s)
  have hs : e (QuotientGroup.mk κ) = s := by rw [hκ, MulEquiv.apply_symm_apply]
  refine ⟨(κ : G), κ.2, ?_⟩
  have hκN : (κ : G) ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer κ.2
  have hk := Hall196.normalizerToPGammaL2Mod_of_mem e (gf_facts hp hq).2.1
    (gf_facts hp hq).2.2.1 (gf_facts hp hq).2.2.2 κ.2
  rw [hs] at hk
  rw [nuG_of_mem hp hq e (Subgroup.mul_mem _ (Subgroup.inv_mem _ hκN) hn)]
  have e1 : (⟨(κ : G)⁻¹ * n, Subgroup.mul_mem _ (Subgroup.inv_mem _ hκN) hn⟩ :
      Subgroup.normalizer (K : Set G)) = ⟨(κ : G), hκN⟩⁻¹ * ⟨n, hn⟩ := rfl
  rw [e1, map_mul, map_inv]
  change (nuK hp hq e ⟨(κ : G), hκN⟩)⁻¹ * α = _
  have hk' : nuK hp hq e ⟨(κ : G), hκN⟩ = SemidirectProduct.inl α.left := by
    rw [hy]
    exact hk
  rw [hk']
  have hα : SemidirectProduct.inl α.left * SemidirectProduct.inr α.right = α :=
    SemidirectProduct.inl_left_mul_inr_right α
  calc (SemidirectProduct.inl α.left)⁻¹ * α =
      (SemidirectProduct.inl α.left)⁻¹ *
        (SemidirectProduct.inl α.left * SemidirectProduct.inr α.right) := by rw [hα]
    _ = SemidirectProduct.inr α.right := inv_mul_cancel_left _ _
    _ = _ := rfl

end Nu

section Lift


end Lift

end CFSG.ClassicalInvolution.Asc77.C25V
