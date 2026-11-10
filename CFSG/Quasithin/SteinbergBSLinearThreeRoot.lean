module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7SecGroup
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aOvergroup
public import CFSG.Quasithin.SteinbergBSCubicPair

public section

namespace CFSG.Quasithin.SteinbergBS

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.QuasithinUnique.Setup.X7a
  CFSG.ComponentClassification CFSG.ABGLocalTools
open scoped MatrixGroups Pointwise

section Coordinates

variable {F : Type} [Field F]

theorem up3_mem_unitriangular (x y z : F) : up3 x y z ∈ LinearFlag.unitriangular 3 F := by
  rw [mem_unitriangular]
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · fin_cases i <;> fin_cases j <;> simp_all [up3_coe, upMat]
  · fin_cases i <;> simp [up3_coe, upMat]

theorem up3_mul_self [CharP F 2] (x y z : F) : up3 x y z * up3 x y z = up3 0 (z * x) 0 := by
  rw [up3_mul, CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero,
    zero_add]

theorem up3_comm_iff (x y z X Y Z : F) :
    up3 x y z * up3 X Y Z = up3 X Y Z * up3 x y z ↔ z * X = Z * x := by
  rw [up3_mul, up3_mul]
  constructor
  · intro h
    obtain ⟨-, h2, -⟩ := up3_inj h
    linear_combination h2
  · intro h
    rw [add_comm x X, add_comm z Z, add_comm y Y, h]


@[expose] def uniCenter (F : Type) [Field F] : Subgroup SL(3, F) where
  carrier := Set.range fun y : F => up3 0 y 0
  one_mem' := ⟨0, up3_zero⟩
  mul_mem' := by
    rintro _ _ ⟨y, rfl⟩ ⟨Y, rfl⟩
    exact ⟨y + Y, by rw [up3_mul]; simp⟩
  inv_mem' := by
    rintro _ ⟨y, rfl⟩
    refine ⟨-y, (inv_eq_of_mul_eq_one_right ?_).symm⟩
    rw [up3_mul]
    simp [up3_zero]


theorem mem_uniCenter {g : SL(3, F)} : g ∈ uniCenter F ↔ ∃ y, g = up3 0 y 0 :=
  ⟨fun ⟨y, hy⟩ => ⟨y, hy.symm⟩, fun ⟨y, h⟩ => ⟨y, h.symm⟩⟩

theorem proj_injOn_unitriangular {u v : SL(3, F)} (hu : u ∈ LinearFlag.unitriangular 3 F)
    (hv : v ∈ LinearFlag.unitriangular 3 F) (h : proj 3 F u = proj 3 F v) : u = v := by
  have h3 : u⁻¹ * v ∈ LinearFlag.unitriangular 3 F ⊓ scalars 3 F :=
    Subgroup.mem_inf.2 ⟨mul_mem (inv_mem hu) hv, proj_eq_proj_iff.1 h⟩
  rw [unitriangular_inf_scalars, mem_bot] at h3
  exact inv_mul_eq_one.1 h3

theorem exists_up3_of_mem_projUnitriangular {g : projectiveSL 3 F}
    (hg : g ∈ projUnitriangular 3 F) : ∃ x y z : F, g = proj 3 F (up3 x y z) := by
  obtain ⟨u, hu, rfl⟩ := hg
  obtain ⟨x, y, z, rfl⟩ := exists_up3_of_mem_unitriangular hu
  exact ⟨x, y, z, rfl⟩

theorem proj_up3_inj {x y z X Y Z : F} (h : proj 3 F (up3 x y z) = proj 3 F (up3 X Y Z)) :
    x = X ∧ y = Y ∧ z = Z :=
  up3_inj (proj_injOn_unitriangular (up3_mem_unitriangular x y z) (up3_mem_unitriangular X Y Z) h)


theorem mem_projCenter_iff {g : projectiveSL 3 F} :
    g ∈ (uniCenter F).map (proj 3 F) ↔
      g ∈ projUnitriangular 3 F ∧ ∀ h ∈ projUnitriangular 3 F, g * h = h * g := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨y, rfl⟩ := mem_uniCenter.1 hu
    refine ⟨mem_map_of_mem _ (up3_mem_unitriangular _ _ _), fun h hh => ?_⟩
    obtain ⟨X, Y, Z, rfl⟩ := exists_up3_of_mem_projUnitriangular hh
    rw [← map_mul, ← map_mul, (up3_comm_iff 0 y 0 X Y Z).2 (by ring)]
  · rintro ⟨hg, hc⟩
    obtain ⟨x, y, z, rfl⟩ := exists_up3_of_mem_projUnitriangular hg
    have hcomm : ∀ X Z : F, z * X = Z * x := fun X Z => by
      have h1 := hc _ (mem_map_of_mem _ (up3_mem_unitriangular X 0 Z))
      rw [← map_mul, ← map_mul] at h1
      exact (up3_comm_iff x y z X 0 Z).1 (proj_injOn_unitriangular
        (mul_mem (up3_mem_unitriangular x y z) (up3_mem_unitriangular X 0 Z))
        (mul_mem (up3_mem_unitriangular X 0 Z) (up3_mem_unitriangular x y z)) h1)
    have hz : z = 0 := by linear_combination hcomm 1 0
    have hx : x = 0 := by linear_combination -(hcomm 0 1)
    rw [hx, hz]
    exact mem_map_of_mem _ (mem_uniCenter.2 ⟨y, rfl⟩)

theorem exists_formula_of_not_mem_semilinear [Finite F] {r : MulAut (projectiveSL 3 F)}
    (hr : r ∉ semilinearAutGroup 3 F) :
    ∃ (D : GL (Fin 3) F) (σ : F ≃+* F), r = conjAut 3 F D * fieldAut 3 F σ * dualAut 3 F := by
  obtain ⟨-, hgen⟩ := automorphism_generation (K := F) (n := 3) (by norm_num)
  obtain ⟨D, σ, ε, hε, hrε⟩ := hgen r
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hε with rfl | rfl
  · refine absurd ?_ hr
    rw [hrε, pow_zero, mul_one]
    exact mul_mem (linearAutGroup_le_semilinearAutGroup (conjAut_mem_linearAutGroup D))
      (fieldAut_mem_semilinearAutGroup σ)
  · exact ⟨D, σ, by rw [hrε, pow_one]⟩

@[expose] noncomputable def gammaZero (F : Type) [Field F] [CharP F 2] :
    MulAut (projectiveSL 3 F) :=
  conjAut 3 F (SpecialLinearGroup.toGL (wJ : SL(3, F))) * dualAut 3 F

theorem gammaZero_apply [CharP F 2] (x y z : F) :
    gammaZero F (proj 3 F (up3 x y z)) = proj 3 F (up3 z (y + z * x) x) := by
  rw [gammaZero, MulAut.mul_apply, dualAut_proj, conjAut_proj, up3_inv]
  congr 1
  apply Subtype.ext
  rw [coe_slConjugation]
  have h1 : ((SpecialLinearGroup.toGL (wJ : SL(3, F)) : GL (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) = wJMat := rfl
  have h2 : (((SpecialLinearGroup.toGL (wJ : SL(3, F)))⁻¹ : GL (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) = wJMat := by
    rw [← map_inv, wJ_inv]
    rfl
  rw [h1, h2]
  show wJMat * (upMat x (y + z * x) z)ᵀ * wJMat = upMat z (y + z * x) x
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply]
  fin_cases i <;> fin_cases j <;> simp [wJMat, upMat]


theorem upperTriangular_of_semilinear_normalizes {A : GL (Fin 3) F} {σ : F ≃+* F}
    (hU : (projUnitriangular 3 F).map (conjAut 3 F A * fieldAut 3 F σ).toMonoidHom =
      projUnitriangular 3 F) :
    ∀ i j : Fin 3, j < i → (A : Matrix (Fin 3) (Fin 3) F) i j = 0 := by
  have hα : conjAut 3 F A * fieldAut 3 F σ ∈ semilinearAutGroup 3 F :=
    mul_mem (linearAutGroup_le_semilinearAutGroup (conjAut_mem_linearAutGroup A))
      (fieldAut_mem_semilinearAutGroup σ)
  have htrans := standard_automorphism_transport (K := F) (n := 3)
  have h7 : ∀ (B : GL (Fin 3) F) (W : Submodule F (Fin 3 → F)),
      (projStabilizer W).map (conjAut 3 F B).toMonoidHom =
        projStabilizer (W.map (mulVecLin (B : Matrix (Fin 3) (Fin 3) F))) :=
    fun B W => htrans.2.2.2.2.2.2.1 B W
  have h8 : ∀ (τ : F ≃+* F) (W : Submodule F (Fin 3 → F)),
      (projStabilizer W).map (fieldAut 3 F τ).toMonoidHom = projStabilizer (coordImage τ W) :=
    fun τ W => htrans.2.2.2.2.2.2.2.1 τ W
  have hflag : ∀ d ≤ 3,
      (flagSpace 3 F d).map (mulVecLin (A : Matrix (Fin 3) (Fin 3) F)) = flagSpace 3 F d := by
    intro d hd
    have h1 := CFSG.QuasithinUnique.Setup.X7Sec.semilinear_flag hα hU hd
    have hmap : (projStabilizer (flagSpace 3 F d)).map
        (conjAut 3 F A * fieldAut 3 F σ).toMonoidHom =
        projStabilizer ((flagSpace 3 F d).map (mulVecLin (A : Matrix (Fin 3) (Fin 3) F))) := by
      rw [CFSG.QuasithinUnique.Setup.Family.map_toMonoidHom_mul, h8,
        CFSG.QuasithinUnique.Setup.X7Sec.coordImage_flagSpace, h7]
    have hle : projUnitriangular 3 F ≤
        projStabilizer ((flagSpace 3 F d).map (mulVecLin (A : Matrix (Fin 3) (Fin 3) F))) := by
      rw [← hmap, h1]
      exact CFSG.QuasithinUnique.Setup.X7Sec.projUnitriangular_le_projStabilizer_flag d
    obtain ⟨m, hm, hW⟩ := eq_flagSpace_of_invariant
      (CFSG.QuasithinUnique.Setup.X7Sec.invariant_of_projUnitriangular_le hle)
    have hdim := CFSG.QuasithinUnique.Setup.Family.finrank_map_mulVecLin_gl A (flagSpace 3 F d)
    rw [hW, finrank_flagSpace hm, finrank_flagSpace hd] at hdim
    rw [hW, hdim]
  intro i j hij
  have h1 := hflag ((j : ℕ) + 1) (by omega)
  have hv : (A : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single j 1 ∈ flagSpace 3 F ((j : ℕ) + 1) := by
    rw [← h1]
    refine ⟨Pi.single j 1, mem_flagSpace.2 fun k hk => ?_, rfl⟩
    rw [Pi.single_eq_of_ne (fun h => by rw [h] at hk; omega)]
  have h2 := mem_flagSpace.1 hv i (by omega)
  rwa [mulVec_single_one, col_apply] at h2

theorem diag_ne_zero_of_upperTriangular {A : GL (Fin 3) F}
    (hA : ∀ i j : Fin 3, j < i → (A : Matrix (Fin 3) (Fin 3) F) i j = 0) (i : Fin 3) :
    (A : Matrix (Fin 3) (Fin 3) F) i i ≠ 0 := by
  have h1 : (A : Matrix (Fin 3) (Fin 3) F).det ≠ 0 := (Matrix.isUnits_det_units A).ne_zero
  have hU : (A : Matrix (Fin 3) (Fin 3) F).IsUpperTriangular := fun _ _ h => hA _ _ h
  rw [Matrix.det_of_isUpperTriangular hU] at h1
  exact Finset.prod_ne_zero_iff.1 h1 i (Finset.mem_univ i)

theorem map_projUnitriangular_gammaZero [CharP F 2] :
    (projUnitriangular 3 F).map (gammaZero F).toMonoidHom = projUnitriangular 3 F := by
  apply le_antisymm
  · rintro _ ⟨g, hg, rfl⟩
    obtain ⟨x, y, z, rfl⟩ := exists_up3_of_mem_projUnitriangular hg
    show gammaZero F _ ∈ _
    rw [gammaZero_apply]
    exact mem_map_of_mem _ (up3_mem_unitriangular _ _ _)
  · intro g hg
    obtain ⟨a, b, c, rfl⟩ := exists_up3_of_mem_projUnitriangular hg
    refine ⟨proj 3 F (up3 c (b + a * c) a), mem_map_of_mem _ (up3_mem_unitriangular _ _ _), ?_⟩
    show gammaZero F _ = _
    rw [gammaZero_apply, add_assoc, CharTwo.add_self_eq_zero, add_zero]

theorem map_inv_eq_of_map_eq {G : Type*} [Group G] {X : Subgroup G} {e : MulAut G}
    (h : X.map e.toMonoidHom = X) : X.map e⁻¹.toMonoidHom = X := by
  conv_lhs => rw [← h]
  rw [← CFSG.QuasithinUnique.Setup.Family.map_toMonoidHom_mul, inv_mul_cancel]
  ext x
  simp

theorem exists_eq_semilinear_mul_gammaZero [Finite F] [CharP F 2]
    {α : MulAut (projectiveSL 3 F)}
    (hαU : (projUnitriangular 3 F).map α.toMonoidHom = projUnitriangular 3 F)
    (hαs : α ∉ semilinearAutGroup 3 F) :
    ∃ (A : GL (Fin 3) F) (σ : F ≃+* F),
      (∀ i j : Fin 3, j < i → (A : Matrix (Fin 3) (Fin 3) F) i j = 0) ∧
        α = conjAut 3 F A * fieldAut 3 F σ * gammaZero F := by
  obtain ⟨A, σ, hα⟩ := exists_formula_of_not_mem_semilinear hαs
  have hAσ : conjAut 3 F A * fieldAut 3 F σ ∈ semilinearAutGroup 3 F :=
    mul_mem (linearAutGroup_le_semilinearAutGroup (conjAut_mem_linearAutGroup A))
      (fieldAut_mem_semilinearAutGroup σ)
  set β := α * (gammaZero F)⁻¹ with hβ
  have hβs : β ∈ semilinearAutGroup 3 F := by
    rw [hβ, hα, gammaZero, _root_.mul_inv_rev,
      show conjAut 3 F A * fieldAut 3 F σ * dualAut 3 F * ((dualAut 3 F)⁻¹ *
        (conjAut 3 F (SpecialLinearGroup.toGL (wJ : SL(3, F))))⁻¹) =
        conjAut 3 F A * fieldAut 3 F σ * (conjAut 3 F (SpecialLinearGroup.toGL wJ))⁻¹ by group]
    exact mul_mem hAσ (inv_mem (linearAutGroup_le_semilinearAutGroup
      (conjAut_mem_linearAutGroup _)))
  have hβU : (projUnitriangular 3 F).map β.toMonoidHom = projUnitriangular 3 F := by
    rw [hβ, CFSG.QuasithinUnique.Setup.Family.map_toMonoidHom_mul,
      map_inv_eq_of_map_eq map_projUnitriangular_gammaZero, hαU]
  obtain ⟨B, τ, hβeq⟩ := mem_semilinearAutGroup_iff.1 hβs
  rw [hβeq] at hβU
  refine ⟨B, τ, upperTriangular_of_semilinear_normalizes hβU, ?_⟩
  rw [← hβeq, hβ, inv_mul_cancel_right]


end Coordinates

section Parabolics

variable {F : Type} [Field F]

theorem projUpperTriangular_le_projStabilizer_flag (d : ℕ) :
    projUpperTriangular 3 F ≤ projStabilizer (flagSpace 3 F d) := by
  rw [projUpperTriangular, projStabilizer, ← flagStabilizer_singleton]
  exact map_mono (upperTriangular_le_flagStabilizer {d})

theorem projStabilizer_inf_eq_projUpperTriangular :
    projStabilizer (flagSpace 3 F 1) ⊓ projStabilizer (flagSpace 3 F 2) =
      projUpperTriangular 3 F := by
  apply le_antisymm
  · rintro x ⟨⟨s, hs, rfl⟩, ⟨t, ht, hts⟩⟩
    have hst : s ∈ stabilizer (flagSpace 3 F 2) := by
      have h1 : t⁻¹ * s ∈ scalars 3 F := proj_eq_proj_iff.1 hts
      have h2 : s = t * (t⁻¹ * s) := by group
      rw [h2]
      exact mul_mem ht (scalars_le_stabilizer _ h1)
    refine ⟨s, fun i j hij => ?_, rfl⟩
    have hd : s ∈ stabilizer (flagSpace 3 F ((j : ℕ) + 1)) := by
      rcases (by omega : (j : ℕ) = 0 ∨ (j : ℕ) = 1) with h | h
      · rw [h]; exact hs
      · rw [h]; exact hst
    have hv : (s : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single j 1 ∈ flagSpace 3 F ((j : ℕ) + 1) := by
      rw [← mem_stabilizer.1 hd]
      refine ⟨Pi.single j 1, mem_flagSpace.2 fun k hk => ?_, rfl⟩
      rw [Pi.single_eq_of_ne (fun h => by rw [h] at hk; omega)]
    have h3 := mem_flagSpace.1 hv i (by omega)
    rwa [mulVec_single_one, col_apply] at h3
  · exact le_inf (projUpperTriangular_le_projStabilizer_flag 1)
      (projUpperTriangular_le_projStabilizer_flag 2)


theorem finrank_coordImage {n : ℕ} (σ : F ≃+* F) (W : Submodule F (Fin n → F)) :
    Module.finrank F (coordImage σ W) = Module.finrank F W := by
  let j : W ≃+ coordImage σ W :=
    { toFun := fun w => ⟨fun i => σ (w.1 i), coord_mem_coordImage w.2⟩
      invFun := fun v => ⟨fun i => σ.symm (v.1 i), v.2⟩
      left_inv := fun w => by ext i; simp
      right_inv := fun v => by ext i; simp
      map_add' := fun v w => by ext i; simp }
  have h := rank_eq_of_equiv_equiv (σ : F → F) j σ.bijective (fun r w => by ext i; simp [j])
  rw [Module.finrank, Module.finrank, h]

theorem map_projStabilizer_of_typeExchanging (D : GL (Fin 3) F) (σ : F ≃+* F)
    (W : Submodule F (Fin 3 → F)) :
    (projStabilizer W).map (conjAut 3 F D * fieldAut 3 F σ * dualAut 3 F).toMonoidHom =
      projStabilizer ((coordImage σ (dotOrth W)).map
        (mulVecLin (D : Matrix (Fin 3) (Fin 3) F))) ∧
    Module.finrank F ((coordImage σ (dotOrth W)).map
        (mulVecLin (D : Matrix (Fin 3) (Fin 3) F))) = 3 - Module.finrank F W := by
  have htrans := standard_automorphism_transport (K := F) (n := 3)
  have h7 : ∀ (B : GL (Fin 3) F) (W : Submodule F (Fin 3 → F)),
      (projStabilizer W).map (conjAut 3 F B).toMonoidHom =
        projStabilizer (W.map (mulVecLin (B : Matrix (Fin 3) (Fin 3) F))) :=
    fun B W => htrans.2.2.2.2.2.2.1 B W
  have h8 : ∀ (τ : F ≃+* F) (W : Submodule F (Fin 3 → F)),
      (projStabilizer W).map (fieldAut 3 F τ).toMonoidHom = projStabilizer (coordImage τ W) :=
    fun τ W => htrans.2.2.2.2.2.2.2.1 τ W
  have h9 : ∀ W : Submodule F (Fin 3 → F),
      (projStabilizer W).map (dualAut 3 F).toMonoidHom = projStabilizer (dotOrth W) :=
    fun W => htrans.2.2.2.2.2.2.2.2.1 W
  refine ⟨?_, ?_⟩
  · rw [CFSG.QuasithinUnique.Setup.Family.map_toMonoidHom_mul,
      CFSG.QuasithinUnique.Setup.Family.map_toMonoidHom_mul, h9, h8, h7]
  · rw [CFSG.QuasithinUnique.Setup.Family.finrank_map_mulVecLin_gl, finrank_coordImage,
      finrank_dotOrth]

end Parabolics

section Inner

variable {G : Type*} [Group G]

theorem aut_mul_conj_mul_inv (s : MulAut G) (x : G) :
    s * MulAut.conj x * s⁻¹ = MulAut.conj (s x) := by
  ext m
  simp [MulAut.conj_apply]

theorem apply_mem_of_mem_normalizer_conj
    (hι : Function.Injective (MulAut.conj : G →* MulAut G)) {X : Subgroup G} {e : MulAut G}
    (he : e ∈ normalizer ((X.map (MulAut.conj : G →* MulAut G) : Subgroup (MulAut G)) :
      Set (MulAut G))) {x : G} (hx : x ∈ X) : e x ∈ X := by
  have h1 := (mem_normalizer_iff.1 he (MulAut.conj x)).1 (mem_map_of_mem _ hx)
  rw [aut_mul_conj_mul_inv] at h1
  exact (mem_map_iff_mem hι).1 h1

theorem map_eq_of_mem_normalizer_conj
    (hι : Function.Injective (MulAut.conj : G →* MulAut G)) {X : Subgroup G} {e : MulAut G}
    (he : e ∈ normalizer ((X.map (MulAut.conj : G →* MulAut G) : Subgroup (MulAut G)) :
      Set (MulAut G))) : X.map e.toMonoidHom = X := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact apply_mem_of_mem_normalizer_conj hι he hx
  · intro x hx
    refine ⟨e⁻¹ x, apply_mem_of_mem_normalizer_conj hι (inv_mem he) hx, ?_⟩
    show e (e⁻¹ x) = x
    rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]

theorem mem_normalizer_of_map_conj_eq {X : Subgroup G} {g : G}
    (h : X.map (MulAut.conj g).toMonoidHom = X) : g ∈ normalizer (X : Set G) := by
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [← h]
    exact ⟨x, hx, rfl⟩
  · intro hx
    rw [← h] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have h1 : g * y * g⁻¹ = g * x * g⁻¹ := hyx
    have h2 : y = x := by simpa using h1
    rwa [← h2]

theorem map_conj_map_conj (X : Subgroup G) (k : G) :
    (X.map (MulAut.conj : G →* MulAut G)).map (MulAut.conj (MulAut.conj k)).toMonoidHom =
      (X.map (MulAut.conj k).toMonoidHom).map (MulAut.conj : G →* MulAut G) := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  refine MonoidHom.ext fun u => ?_
  simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply, map_mul, map_inv]


theorem map_conj_inv_map_conj (Y : Subgroup G) (c : G) :
    (Y.map (MulAut.conj c⁻¹).toMonoidHom).map (MulAut.conj c).toMonoidHom = Y := by
  rw [← CFSG.QuasithinUnique.Setup.Family.map_toMonoidHom_mul, ← map_mul, mul_inv_cancel,
    map_one]
  ext y
  simp


end Inner

section Main

open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_normal)

variable {F : Type} [Field F]


theorem isSylowOf_exists_map_conj {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {P P' D : Subgroup G} (hP : IsSylowOf p P D) (hP' : IsSylowOf p P' D) :
    ∃ x ∈ D, P' = P.map (MulAut.conj x).toMonoidHom := by
  obtain ⟨Q, rfl⟩ := hP
  obtain ⟨Q', rfl⟩ := hP'
  obtain ⟨d, hd⟩ := MulAction.exists_smul_eq D Q Q'
  refine ⟨d, d.2, ?_⟩
  rw [← hd, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
  ext y
  constructor
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨_, ⟨z, hz, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨_, ⟨z, hz, rfl⟩, rfl⟩


end Main


end CFSG.Quasithin.SteinbergBS
