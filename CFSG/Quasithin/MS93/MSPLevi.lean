module

public import CFSG.Quasithin.MS93.MSPOff

public section

namespace CFSG.Quasithin.MS93.MSP

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFour

variable {F : Type} [Field F]

theorem transv_eq_transv_iff [CharP F 2] {x y : V4 F} (hx : x ≠ 0) :
    transv y 1 = transv x 1 ↔ y = x := by
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  obtain ⟨v, hv⟩ := exists_form_eq_one hx
  have h1 := congrArg (fun g : Sp4 F => mat g *ᵥ v) h
  simp only [transv_mulVec, one_mul, hv, one_smul, add_right_inj] at h1
  set l := form F y v with hl
  have hy : y ≠ 0 := by
    rintro rfl
    rw [smul_zero] at h1
    exact hx h1.symm
  rw [← h1, transv_smul_vec] at h
  have hl2 : l ^ 2 * 1 = 1 := transv_injective hy h.symm |>.symm.trans rfl |>.symm
  have hl1 : l = 1 := by
    have h2 : (l - 1) ^ 2 = 0 := by
      have h2z : (2 : F) = 0 := CharTwo.two_eq_zero
      linear_combination hl2 + (1 - l) * h2z
    exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h2)
  rw [← h1, hl1, one_smul]

theorem mulVec_eq_of_commute_transv [CharP F 2] {g : Sp4 F} {x : V4 F} (hx : x ≠ 0)
    (h : g * transv x 1 = transv x 1 * g) : mat g *ᵥ x = x := by
  have : g * transv x 1 * g⁻¹ = transv x 1 := by rw [h, mul_inv_cancel_right]
  rw [transv_conj] at this
  exact (transv_eq_transv_iff hx).1 this

theorem Q₂_comm [CharP F 2] {x y : Sp4 F} (hx : x ∈ Q₂ F) (hy : y ∈ Q₂ F) : x * y = y * x := by
  obtain ⟨hxS, hx0⟩ := mem_Q₂_iff.1 hx
  obtain ⟨hyS, hy0⟩ := mem_Q₂_iff.1 hy
  obtain ⟨a, C, hC, hxC⟩ := exists_of_mem_sylS hxS
  obtain ⟨b, E, hE, hyE⟩ := exists_of_mem_sylS hyS
  have hC11 : C 1 1 = 0 := by rw [← entry_of_mem_sylS hxC, hx0]
  have hE11 : E 1 1 = 0 := by rw [← entry_of_mem_sylS hyE, hy0]
  have hC10 : C 1 0 = C 0 1 := by simpa using congrFun₂ hC 0 1
  have hE10 : E 1 0 = E 0 1 := by simpa using congrFun₂ hE 0 1
  refine ext_mulVec fun v => ?_
  rw [mat_mul_mulVec, mat_mul_mulVec, hxC, hyE]
  obtain ⟨p0, p1, p2, p3⟩ := mulVec_blockMat_unitri b E v
  obtain ⟨r0, r1, r2, r3⟩ := mulVec_blockMat_unitri a C v
  obtain ⟨s0, s1, s2, s3⟩ := mulVec_blockMat_unitri a C (blockMat (unitri b) E *ᵥ v)
  obtain ⟨t0, t1, t2, t3⟩ := mulVec_blockMat_unitri b E (blockMat (unitri a) C *ᵥ v)
  refine ext4 ?_ ?_ ?_ ?_
  · rw [s0, t0, p0, p1, p2, p3, r0, r1, r2, r3, hC11, hE11, hC10, hE10]
    grind
  · rw [s1, t1, p1, p2, p3, r1, r2, r3, hC11, hE11, hC10, hE10]
    grind
  · rw [s2, t2, p2, r2]
  · rw [s3, t3, p2, p3, r2, r3]
    grind


abbrev hp₁ (F : Type) [Field F] : Submodule F (V4 F) := Submodule.span F {e₁ F, f₁ F}

abbrev lev₂ (F : Type) [Field F] : Subgroup (Sp4 F) := fixer (hp₁ F)

abbrev L₂ (F : Type) [Field F] : Subgroup (Sp4 F) := Q₂ F ⊔ lev₂ F

theorem mem_lev₂_iff {g : Sp4 F} :
    g ∈ lev₂ F ↔ mat g *ᵥ e₁ F = e₁ F ∧ mat g *ᵥ f₁ F = f₁ F := by
  refine ⟨fun h => ⟨h _ (Submodule.subset_span (Set.mem_insert _ _)),
    h _ (Submodule.subset_span (Set.mem_insert_of_mem _ rfl))⟩, fun ⟨h1, h2⟩ v hv => ?_⟩
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.1 hv
  rw [mulVec_add, mulVec_smul, mulVec_smul, h1, h2]

theorem lev₂_le_P₂ : lev₂ F ≤ P₂ F := fun g hg =>
  fixer_le_stab _ (fun v hv => by
    rw [pt₀_eq_span] at hv
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hv
    rw [mulVec_smul, (mem_lev₂_iff.1 hg).1])

theorem L₂_le_P₂ : L₂ F ≤ P₂ F := sup_le Q₂_le_P₂ lev₂_le_P₂

theorem Q₂_le_L₂ : Q₂ F ≤ L₂ F := le_sup_left


theorem transv_mem_L₂ {x : V4 F} (hx : x (.inr 0) = 0) (c : F) : transv x c ∈ L₂ F := by
  set x' : V4 F := x - x (.inl 0) • e₁ F with hx'
  have hlev : transv x' c ∈ lev₂ F := mem_lev₂_iff.2 ⟨by
      rw [transv_mulVec, form_apply]
      simp [hx', hx], by
      rw [transv_mulVec, form_apply]
      simp [hx']⟩
  have hQ : transv x c * transv x' (-c) ∈ Q₂ F := by
    refine ⟨fun v hv => ?_, fun v hv => ?_⟩
    · obtain ⟨h1, h2, h3⟩ := mem_pt₀.1 hv
      rw [mat_mul_mulVec, transv_mulVec, transv_mulVec]
      refine ext4 ?_ ?_ ?_ ?_ <;> simp [form_apply, hx', h1, h2, h3, hx]
    · have h0 := mem_perp_pt₀.1 hv
      rw [mat_mul_mulVec, transv_mulVec, transv_mulVec]
      refine mem_pt₀.2 ⟨?_, ?_, ?_⟩ <;> simp [form_apply, hx', h0, hx] <;> ring
  have : transv x c = (transv x c * transv x' (-c)) * transv x' c := by
    rw [mul_assoc, transv_mul, neg_add_cancel, transv_zero, mul_one]
  rw [this]
  exact Subgroup.mul_mem_sup hQ hlev

theorem L₂_le_normalizer_Q₂ : L₂ F ≤ Subgroup.normalizer (Q₂ F : Set (Sp4 F)) :=
  L₂_le_P₂.trans P₂_le_normalizer_Q₂


@[expose] def iotaM (M : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
  fromBlocks !![1, 0; 0, M 0 0] !![0, 0; 0, M 0 1] !![0, 0; 0, M 1 0] !![1, 0; 0, M 1 1]

theorem iotaM_mulVec (M : Matrix (Fin 2) (Fin 2) F) (v : V4 F) :
    iotaM M *ᵥ v = v (.inl 0) • e₁ F + (M 0 0 * v (.inl 1) + M 0 1 * v (.inr 1)) • e₂ F +
      v (.inr 0) • f₁ F + (M 1 0 * v (.inl 1) + M 1 1 * v (.inr 1)) • f₂ F := by
  rw [iotaM, fromBlocks_mulVec]
  refine ext4 ?_ ?_ ?_ ?_ <;> simp [dotProduct, Fin.sum_univ_two]

theorem iotaM_mul (M N : Matrix (Fin 2) (Fin 2) F) : iotaM M * iotaM N = iotaM (M * N) := by
  refine mat_ext_mulVec fun v => ?_
  rw [← mulVec_mulVec, iotaM_mulVec, iotaM_mulVec, iotaM_mulVec]
  refine ext4 ?_ ?_ ?_ ?_ <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem iotaM_one : iotaM (1 : Matrix (Fin 2) (Fin 2) F) = 1 := by
  refine mat_ext_mulVec fun v => ?_
  rw [iotaM_mulVec, one_mulVec]
  refine ext4 ?_ ?_ ?_ ?_ <;> simp

theorem iotaM_isom (M : Matrix.SpecialLinearGroup (Fin 2) F) (u v : V4 F) :
    form F (iotaM M *ᵥ u) (iotaM M *ᵥ v) = form F u v := by
  have hdet : (M : Matrix (Fin 2) (Fin 2) F) 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
    have := M.2
    rwa [det_fin_two] at this
  rw [iotaM_mulVec, iotaM_mulVec, form_apply, form_apply]
  simp
  linear_combination (u (.inl 1) * v (.inr 1) - u (.inr 1) * v (.inl 1)) * hdet

@[expose] noncomputable def levHom₂ : Matrix.SpecialLinearGroup (Fin 2) F →* Sp4 F where
  toFun M := ofMat (iotaM M) (iotaM (M⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F))
    (by rw [iotaM_mul, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one, iotaM_one])
    (by rw [iotaM_mul, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one, iotaM_one]) (iotaM_isom M)
  map_one' := mat_injective (by rw [mat_ofMat, Matrix.SpecialLinearGroup.coe_one, iotaM_one,
    mat_one])
  map_mul' M N := mat_injective (by rw [mat_ofMat, mat_mul, mat_ofMat, mat_ofMat, iotaM_mul,
    Matrix.SpecialLinearGroup.coe_mul])

theorem mat_levHom₂ (M : Matrix.SpecialLinearGroup (Fin 2) F) : mat (levHom₂ M) = iotaM M :=
  rfl

theorem levHom₂_injective : Function.Injective (levHom₂ (F := F)) := by
  intro M N h
  have h' := congrArg (fun g => mat g) h
  simp only [mat_levHom₂] at h'
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [iotaM] using congrFun₂ h' (.inl 1) (.inl 1)
  · simpa [iotaM] using congrFun₂ h' (.inl 1) (.inr 1)
  · simpa [iotaM] using congrFun₂ h' (.inr 1) (.inl 1)
  · simpa [iotaM] using congrFun₂ h' (.inr 1) (.inr 1)

theorem range_levHom₂ : (levHom₂ (F := F)).range = lev₂ F := by
  refine le_antisymm ?_ fun g hg => ?_
  · rintro _ ⟨M, rfl⟩
    refine mem_lev₂_iff.2 ⟨?_, ?_⟩ <;> rw [mat_levHom₂, iotaM_mulVec] <;>
      refine ext4 ?_ ?_ ?_ ?_ <;> simp
  · obtain ⟨h1, h2⟩ := mem_lev₂_iff.1 hg
    have hperp : ∀ w : V4 F, w (.inl 0) = 0 → w (.inr 0) = 0 →
        (mat g *ᵥ w) (.inl 0) = 0 ∧ (mat g *ᵥ w) (.inr 0) = 0 := by
      intro w hw0 hw2
      have hB1 := form_mat g (e₁ F) w
      have hB2 := form_mat g (f₁ F) w
      rw [h1, form_apply, form_apply] at hB1
      rw [h2, form_apply, form_apply] at hB2
      simp [hw0, hw2] at hB1 hB2
      exact ⟨hB2, hB1⟩
    obtain ⟨a0, a2⟩ := hperp (e₂ F) (by simp) (by simp)
    obtain ⟨b0, b2⟩ := hperp (f₂ F) (by simp) (by simp)
    obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin 2) (Fin 2) F,
        M = !![(mat g *ᵥ e₂ F) (.inl 1), (mat g *ᵥ f₂ F) (.inl 1);
          (mat g *ᵥ e₂ F) (.inr 1), (mat g *ᵥ f₂ F) (.inr 1)] := ⟨_, rfl⟩
    have hdet : M.det = 1 := by
      have := form_mat g (e₂ F) (f₂ F)
      rw [form_apply, form_apply] at this
      simp [a0, a2, b0, b2] at this
      rw [det_fin_two, hM]
      simp
      linear_combination this
    refine ⟨⟨M, hdet⟩, ext_mulVec fun v => ?_⟩
    change iotaM M *ᵥ v = _
    rw [iotaM_mulVec]
    have hv : v = v (.inl 0) • e₁ F + v (.inl 1) • e₂ F + v (.inr 0) • f₁ F +
        v (.inr 1) • f₂ F := by
      refine ext4 ?_ ?_ ?_ ?_ <;> simp
    conv_rhs => rw [hv]
    rw [mulVec_add, mulVec_add, mulVec_add, mulVec_smul, mulVec_smul, mulVec_smul, mulVec_smul,
      h1, h2]
    have a0' : mat g (.inl 0) (.inl 1) = 0 := by simpa using a0
    have a2' : mat g (.inr 0) (.inl 1) = 0 := by simpa using a2
    have b0' : mat g (.inl 0) (.inr 1) = 0 := by simpa using b0
    have b2' : mat g (.inr 0) (.inr 1) = 0 := by simpa using b2
    refine ext4 ?_ ?_ ?_ ?_ <;> simp [hM, a0', a2', b0', b2'] <;> ring


@[expose] noncomputable def levHom₁ : Matrix.SpecialLinearGroup (Fin 2) F →* Sp4 F :=
  SymplecticTorusWeyl.leviSp.comp Matrix.SpecialLinearGroup.toGL

theorem mat_levHom₁ (A : Matrix.SpecialLinearGroup (Fin 2) F) :
    mat (levHom₁ A) = fromBlocks (A : Matrix (Fin 2) (Fin 2) F) 0 0
      ((A⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)ᵀ := by
  rw [levHom₁, MonoidHom.comp_apply, mat, SymplecticTorusWeyl.coe_leviSp]
  simp only [Matrix.SpecialLinearGroup.coe_inv]
  congr 2

noncomputable abbrev lev₁ (F : Type) [Field F] : Subgroup (Sp4 F) := (levHom₁ (F := F)).range

noncomputable abbrev L₁ (F : Type) [Field F] : Subgroup (Sp4 F) := Q₁ F ⊔ lev₁ F

theorem levHom₁_injective : Function.Injective (levHom₁ (F := F)) := by
  intro A B h
  have h' := congrArg (fun g => mat g) h
  simp only [mat_levHom₁] at h'
  exact Subtype.ext (fromBlocks_inj.1 h').1

theorem lev₁_le_P₁ : lev₁ F ≤ P₁ F := by
  rintro _ ⟨A, rfl⟩
  refine mem_stab_of_le fun v hv => ?_
  obtain ⟨h0, h1⟩ := mem_ln₀.1 hv
  have hr : v ∘ Sum.inr = 0 := funext fun j => by fin_cases j <;> simp [h0, h1]
  refine mem_ln₀.2 ⟨?_, ?_⟩ <;> rw [mat_levHom₁, fromBlocks_mulVec, hr] <;> simp

theorem L₁_le_P₁ : L₁ F ≤ P₁ F := sup_le Q₁_le_P₁ lev₁_le_P₁

theorem Q₁_le_L₁ : Q₁ F ≤ L₁ F := le_sup_left

theorem lev₁_le_L₁ : lev₁ F ≤ L₁ F := le_sup_right

theorem L₁_le_normalizer_Q₁ : L₁ F ≤ Subgroup.normalizer (Q₁ F : Set (Sp4 F)) :=
  L₁_le_P₁.trans P₁_le_normalizer_Q₁

theorem Q₁_inf_lev₁ : Q₁ F ⊓ lev₁ F = ⊥ := by
  refine eq_bot_iff.2 fun g hg => ?_
  obtain ⟨hgQ, A, rfl⟩ := Subgroup.mem_inf.1 hg
  have hA : (A : Matrix (Fin 2) (Fin 2) F) = 1 := by
    have hfix : ∀ j : Fin 2, mat (levHom₁ A) *ᵥ Pi.single (.inl j) 1 = Pi.single (.inl j) 1 :=
      fun j => hgQ _ (mem_ln₀.2 ⟨by simp, by simp⟩)
    ext i j
    have := congrFun (hfix j) (.inl i)
    rw [mat_levHom₁, fromBlocks_mulVec] at this
    fin_cases i <;> fin_cases j <;>
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.single_apply] using this
  rw [Subgroup.mem_bot, show A = 1 from Subtype.ext hA, map_one]

theorem levHom₁_conj_tau (A : Matrix.SpecialLinearGroup (Fin 2) F)
    {C : Matrix (Fin 2) (Fin 2) F} (hC : Cᵀ = C) :
    levHom₁ A * tau hC * (levHom₁ A)⁻¹ = tau (C := (A : Matrix (Fin 2) (Fin 2) F) * C *
      (A : Matrix (Fin 2) (Fin 2) F)ᵀ)
      (by rw [transpose_mul, transpose_mul, transpose_transpose, hC, Matrix.mul_assoc]) := by
  refine mat_injective ?_
  rw [mat_mul, mat_mul, ← map_inv, mat_levHom₁, mat_levHom₁, inv_inv, mat_tau, mat_tau,
    blockMat, blockMat, unitri_zero, inv_one, transpose_one, Matrix.one_mul, Matrix.one_mul,
    fromBlocks_multiply, fromBlocks_multiply]
  have h1 : (A : Matrix (Fin 2) (Fin 2) F) *
      ((A⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have h2 : ((A⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)ᵀ *
      (A : Matrix (Fin 2) (Fin 2) F)ᵀ = 1 := by
    rw [← transpose_mul, h1, transpose_one]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one, h1, h2,
    Matrix.mul_assoc]

@[expose] noncomputable def shortHom : Multiplicative F →* Sp4 F where
  toFun c := tau (sym2_transpose 0 (Multiplicative.toAdd c) 0)
  map_one' := mat_injective (by
    rw [mat_tau, mat_one, unitri_zero]
    convert blockMat_one using 2
    ext i j
    fin_cases i <;> fin_cases j <;> rfl)
  map_mul' c d := by
    rw [tau_mul_tau]
    exact tau_congr _ _ (by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [sym2])

noncomputable abbrev X₁ (F : Type) [Field F] : Subgroup (Sp4 F) := (shortHom (F := F)).range


theorem normalizer_qLine {l : Submodule F (V4 F)} (hl : IsLine l) :
    Subgroup.normalizer (qLine l : Set (Sp4 F)) = stab l := by
  refine le_antisymm ?_ (stab_le_normalizer_fixer l)
  have h := normalizer_le_stab_fixSp (qLine l)
  rwa [fixSp_qLine hl] at h


theorem normalizer_xPoint {p : Submodule F (V4 F)} (hp : IsPoint p) :
    Subgroup.normalizer (xPoint p : Set (Sp4 F)) = stab p := by
  refine le_antisymm ?_ (stab_le_normalizer_xPoint p)
  have h := normalizer_le_stab_fixSp (xPoint p)
  rwa [fixSp_xPoint hp, stab_perp] at h

theorem normalizer_Q₁ : Subgroup.normalizer (Q₁ F : Set (Sp4 F)) = P₁ F :=
  normalizer_qLine isLine_ln₀


@[expose] def wJ (F : Type) [Field F] : Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨!![0, 1; -1, 0], by simp [det_fin_two]⟩

theorem levHom₁_wJ_not_mem_P₂ : levHom₁ (wJ F) ∉ P₂ F := by
  intro h
  have he : e₁ F ∈ pt₀ F := by rw [pt₀_eq_span]; exact Submodule.mem_span_singleton_self _
  have := (mem_pt₀.1 (mulVec_mem_of_mem_stab h he)).1
  rw [mat_levHom₁, fromBlocks_mulVec] at this
  simp [wJ, dotProduct, Fin.sum_univ_two] at this

theorem levHom₂_wJ_not_mem_P₁ : levHom₂ (wJ F) ∉ P₁ F := by
  intro h
  have he : e₂ F ∈ ln₀ F := mem_ln₀.2 ⟨by simp, by simp⟩
  have := (mem_ln₀.1 (mulVec_mem_of_mem_stab h he)).2
  rw [mat_levHom₂, iotaM_mulVec] at this
  simp [wJ] at this

theorem not_P₁_le_borel : ¬ P₁ F ≤ borel F := fun h =>
  levHom₁_wJ_not_mem_P₂ (borel_le_P₂ (h (lev₁_le_P₁ ⟨wJ F, rfl⟩)))

theorem levHom₂_wJ_mem_lev₂ : levHom₂ (wJ F) ∈ lev₂ F := by
  rw [← range_levHom₂]
  exact ⟨wJ F, rfl⟩

theorem not_P₂_le_borel : ¬ P₂ F ≤ borel F := fun h =>
  levHom₂_wJ_not_mem_P₁ (borel_le_P₁ (h (lev₂_le_P₂ levHom₂_wJ_mem_lev₂)))


end CFSG.Quasithin.MS93.MSP
