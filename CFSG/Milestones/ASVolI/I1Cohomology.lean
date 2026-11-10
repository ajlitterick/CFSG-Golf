module

public import CFSG.Milestones.ASVolI.I1
public import CFSG.Quasithin.SteinbergCBI16

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ASVolI

open CFSG.Open CFSG.Blueprint CFSG.ASVolI.ChIJK
open scoped MatrixGroups


section JPHelpers


end JPHelpers


section G2Model

variable (K : Type) [Field K] [CharP K 2]


end G2Model

section G2Coords

variable (K : Type) [Field K] [CharP K 2]


end G2Coords

section G2Model2

variable (K : Type) [Field K] [CharP K 2] [Algebra (ZMod 2) K]


end G2Model2

section G2Model3

variable (K : Type) [Field K] [CharP K 2] [Algebra (ZMod 2) K]


end G2Model3

section G2Finite

variable (K : Type) [Field K] [Finite K] [Algebra (ZMod 2) K]


end G2Finite

section JPHelpers2


end JPHelpers2

section QuadExt

open Polynomial in
theorem burnsideI16h_exists_quad_ext {K : Type} [Field K] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ∃ (F : Type) (_ : Field F) (_ : Algebra K F) (ω : F),
      Module.finrank K F = 2 ∧ ω ^ 2 + algebraMap K F b * ω + algebraMap K F c = 0 := by
  have hdeg : (X ^ 2 + C b * X + C c : K[X]).natDegree = 2 := by compute_degree!
  have hirr' : Irreducible (X ^ 2 + C b * X + C c : K[X]) := by
    apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
    · rw [hdeg]; simp
    · intro s hs
      apply hirr s
      simpa using hs
  haveI : Fact (Irreducible (X ^ 2 + C b * X + C c : K[X])) := ⟨hirr'⟩
  refine ⟨AdjoinRoot (X ^ 2 + C b * X + C c : K[X]), inferInstance, inferInstance,
    AdjoinRoot.root _, ?_, ?_⟩
  · rw [PowerBasis.finrank (AdjoinRoot.powerBasis hirr'.ne_zero)]
    simp [hdeg]
  · have := AdjoinRoot.eval₂_root (X ^ 2 + C b * X + C c : K[X])
    simpa using this

end QuadExt

section QuadField

open CFSG.Quasithin CFSG.Quasithin.JonesParshall

variable {K : Type} [Field K] [Fintype K] [CharP K 2]
  {F : Type} [Field F] [Fintype F] [Algebra K F] [CharP F 2]

theorem burnsideI16h_sig_alg {n : ℕ} (hK : Fintype.card K = 2 ^ n) (k : K) :
    sig n (algebraMap K F k) = algebraMap K F k := by
  rw [sig_apply, ← map_pow, ← hK, FiniteField.pow_card]

theorem burnsideI16h_sig_fixed {n : ℕ} (hK : Fintype.card K = 2 ^ n) (hn : 1 ≤ n) {x : F}
    (hx : sig n x = x) : ∃ k : K, algebraMap K F k = x := by
  classical
  have hq1 : 1 < 2 ^ n := Nat.one_lt_two_pow (by omega)
  let S : Finset F := Finset.univ.filter (fun x : F => x ^ 2 ^ n = x)
  let T : Finset F := Finset.univ.image (algebraMap K F)
  have hTS : T ⊆ S := by
    intro y hy
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hy
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
    have := burnsideI16h_sig_alg (F := F) hK k
    rwa [sig_apply] at this
  have hTc : T.card = 2 ^ n := by
    rw [Finset.card_image_of_injective _ (algebraMap K F).injective, Finset.card_univ, hK]
  have hSc : S.card ≤ 2 ^ n := by
    have h := Polynomial.card_le_degree_of_subset_roots
      (p := (Polynomial.X ^ 2 ^ n - Polynomial.X : Polynomial F)) (Z := S) (by
        intro y hy
        rw [Polynomial.mem_roots (FiniteField.X_pow_card_sub_X_ne_zero F hq1)]
        have hy' := (Finset.mem_filter.1 hy).2
        simp [Polynomial.IsRoot, hy'])
    rwa [FiniteField.X_pow_card_sub_X_natDegree_eq F hq1] at h
  have hTS' : T = S := Finset.eq_of_subset_of_card_le hTS (by omega)
  have hxS : x ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ _, by rwa [sig_apply] at hx⟩
  rw [← hTS'] at hxS
  obtain ⟨k, -, hk⟩ := Finset.mem_image.1 hxS
  exact ⟨k, hk⟩

variable {b c : K}

theorem burnsideI16h_sig_omega {n : ℕ} (hK : Fintype.card K = 2 ^ n) (hn : 1 ≤ n) {ω : F}
    (hω : ω ^ 2 + algebraMap K F b * ω + algebraMap K F c = 0)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) : sig n ω = ω + algebraMap K F b := by
  have h2c : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have h1 : (sig n ω) ^ 2 + algebraMap K F b * sig n ω + algebraMap K F c = 0 := by
    have := congrArg (sig n) hω
    simpa [map_add, map_mul, map_pow, burnsideI16h_sig_alg (F := F) hK] using this
  have h3 : (sig n ω + ω) * (sig n ω + ω + algebraMap K F b) = 0 := by
    linear_combination h1 + hω + (sig n ω * ω - algebraMap K F c) * h2c
  rcases mul_eq_zero.1 h3 with h | h
  · exfalso
    have hfix : sig n ω = ω := CharTwo.add_eq_zero.1 h
    obtain ⟨k, hk⟩ := burnsideI16h_sig_fixed hK hn hfix
    apply hirr k
    apply (algebraMap K F).injective
    rw [map_zero, map_add, map_add, map_mul, map_pow, hk]
    exact hω
  · have := CharTwo.add_eq_zero.1 h
    linear_combination this - ω * h2c

end QuadField

section Setup

open CFSG.Quasithin CFSG.Quasithin.JonesParshall

structure burnsideI16h_Setup (K F : Type) [Field K] [Fintype K] [CharP K 2] [Field F] [Fintype F]
    [Algebra K F] [CharP F 2] where
  n : ℕ
  b : K
  c : K
  hn : 1 ≤ n
  hK : Fintype.card K = 2 ^ n
  ω : F
  hω : ω ^ 2 + algebraMap K F b * ω + algebraMap K F c = 0
  hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0
  hrank : Module.finrank K F = 2

variable {K F : Type} [Field K] [Fintype K] [CharP K 2] [Field F] [Fintype F] [Algebra K F]
  [CharP F 2] (S : burnsideI16h_Setup K F)

@[expose] noncomputable def burnsideI16h_coordMap (ω : F) : (K × K) →ₗ[K] F :=
  (Algebra.linearMap K F).coprod (LinearMap.toSpanSingleton K F ω)

theorem burnsideI16h_coordMap_apply (ω : F) (u v : K) :
    burnsideI16h_coordMap ω (u, v) = algebraMap K F u + algebraMap K F v * ω := by
  simp [burnsideI16h_coordMap, Algebra.smul_def]

theorem burnsideI16h_coordMap_bijective : Function.Bijective (burnsideI16h_coordMap (K := K) S.ω) := by
  have hinj : Function.Injective (burnsideI16h_coordMap (K := K) S.ω) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨u, v⟩ h
    rw [burnsideI16h_coordMap_apply] at h
    have hv : v = 0 := by
      by_contra hv0
      have hv0' : algebraMap K F v ≠ 0 := (map_ne_zero_iff _ (algebraMap K F).injective).2 hv0
      have hω' : S.ω = algebraMap K F (-u / v) := by
        rw [map_div₀, map_neg]
        field_simp
        linear_combination h
      refine S.hirr (-u / v) ((algebraMap K F).injective ?_)
      rw [map_zero, map_add, map_add, map_mul, map_pow, ← hω']
      exact S.hω
    subst hv
    simp only [map_zero, zero_mul, add_zero] at h
    have hu : u = 0 := (algebraMap K F).injective (by rw [h, map_zero])
    rw [hu]
    rfl
  refine ⟨hinj, ?_⟩
  have hcard : Nat.card F = Nat.card (K × K) := by
    rw [Module.natCard_eq_pow_finrank (K := K) (V := F), S.hrank, Nat.card_prod, sq]
  exact (Function.Injective.bijective_of_nat_card_le hinj hcard.le).2

@[expose] noncomputable def burnsideI16h_ocoordEquiv : (K × K) ≃ₗ[K] F :=
  LinearEquiv.ofBijective _ (burnsideI16h_coordMap_bijective S)

theorem burnsideI16h_ocoordEquiv_apply (u v : K) :
    burnsideI16h_ocoordEquiv S (u, v) = algebraMap K F u + algebraMap K F v * S.ω :=
  burnsideI16h_coordMap_apply S.ω u v

theorem burnsideI16h_coord_spec (z : F) :
    algebraMap K F ((burnsideI16h_ocoordEquiv S).symm z).1 +
      algebraMap K F ((burnsideI16h_ocoordEquiv S).symm z).2 * S.ω = z := by
  set p := (burnsideI16h_ocoordEquiv S).symm z with hp
  have h : burnsideI16h_ocoordEquiv S p = z := (burnsideI16h_ocoordEquiv S).apply_symm_apply z
  rw [← h]
  exact (burnsideI16h_ocoordEquiv_apply S p.1 p.2).symm

end Setup

section Hermitian

open CFSG.Quasithin CFSG.Quasithin.JonesParshall Matrix

variable {K F : Type} [Field K] [Fintype K] [CharP K 2] [Field F] [Fintype F] [Algebra K F]
  [CharP F 2] (S : burnsideI16h_Setup K F)

abbrev burnsideI16h_OI : Type := Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2

theorem burnsideI16h_fin1 (i : Fin (2 - 1)) : i = 0 := Fin.fin_one_eq_zero i

theorem burnsideI16h_hF : Fintype.card F = 2 ^ (2 * S.n) := by
  rw [Module.card_eq_pow_finrank (K := K) (V := F), S.hrank, S.hK, ← pow_mul, mul_comm]

theorem burnsideI16h_hσ : ∀ x : F, sig S.n (sig S.n x) = x := sig_sig (burnsideI16h_hF S)

theorem burnsideI16h_sig_coord (u v : K) :
    sig S.n (algebraMap K F u + algebraMap K F v * S.ω) =
      algebraMap K F u + algebraMap K F v * (S.ω + algebraMap K F S.b) := by
  rw [map_add, map_mul, burnsideI16h_sig_alg (F := F) S.hK, burnsideI16h_sig_alg (F := F) S.hK,
    burnsideI16h_sig_omega S.hK S.hn S.hω S.hirr]

theorem burnsideI16h_norm_coord (u v : K) :
    (algebraMap K F u + algebraMap K F v * S.ω) *
        sig S.n (algebraMap K F u + algebraMap K F v * S.ω) =
      algebraMap K F (u ^ 2 + S.b * u * v + S.c * v ^ 2) := by
  have h2c : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [burnsideI16h_sig_coord S]
  simp only [map_add, map_mul, map_pow]
  linear_combination (algebraMap K F v) ^ 2 * S.hω +
    (algebraMap K F u * algebraMap K F v * S.ω - algebraMap K F S.c * algebraMap K F v ^ 2) * h2c

@[expose] noncomputable def burnsideI16h_c0 : F →ₗ[K] K :=
  (LinearMap.fst K K K).comp (burnsideI16h_ocoordEquiv S).symm.toLinearMap

@[expose] noncomputable def burnsideI16h_c1 : F →ₗ[K] K :=
  (LinearMap.snd K K K).comp (burnsideI16h_ocoordEquiv S).symm.toLinearMap

theorem burnsideI16h_coord_symm (u v : K) :
    (burnsideI16h_ocoordEquiv S).symm (algebraMap K F u + algebraMap K F v * S.ω) = (u, v) := by
  rw [← burnsideI16h_ocoordEquiv_apply, LinearEquiv.symm_apply_apply]

theorem burnsideI16h_c0_coord (u v : K) :
    burnsideI16h_c0 S (algebraMap K F u + algebraMap K F v * S.ω) = u := by
  simp [burnsideI16h_c0, burnsideI16h_coord_symm S]

theorem burnsideI16h_c1_coord (u v : K) :
    burnsideI16h_c1 S (algebraMap K F u + algebraMap K F v * S.ω) = v := by
  simp [burnsideI16h_c1, burnsideI16h_coord_symm S]

theorem burnsideI16h_c0_alg (x : K) : burnsideI16h_c0 S (algebraMap K F x) = x := by
  have := burnsideI16h_c0_coord S x 0
  simpa using this

@[expose] noncomputable def burnsideI16h_zf (u v : K) : F :=
  algebraMap K F u + algebraMap K F v * S.ω

@[expose] noncomputable def burnsideI16h_hmat (x y u v : K) : Matrix (Fin 2) (Fin 2) F :=
  !![algebraMap K F x, burnsideI16h_zf S u v; sig S.n (burnsideI16h_zf S u v), algebraMap K F y]

@[expose] noncomputable def burnsideI16h_H : (burnsideI16h_OI → K) →ₗ[K] Matrix (Fin 2) (Fin 2) F where
  toFun w := burnsideI16h_hmat S (w (Sum.inl 0)) (w (Sum.inr (Sum.inl 0)))
    (w (Sum.inr (Sum.inr 0))) (w (Sum.inr (Sum.inr 1)))
  map_add' w w' := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [burnsideI16h_hmat, burnsideI16h_zf, add_mul, add_add_add_comm]
  map_smul' k w := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [burnsideI16h_hmat, burnsideI16h_zf, Algebra.smul_def, mul_add, mul_assoc,
        burnsideI16h_sig_alg (F := F) S.hK]

theorem burnsideI16h_H_mem (w : burnsideI16h_OI → K) : burnsideI16h_H S w ∈ hermA S.n F := by
  refine mem_hermA_of fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [burnsideI16h_H, burnsideI16h_hmat, burnsideI16h_zf, burnsideI16h_hσ S,
      burnsideI16h_sig_alg (F := F) S.hK]

@[expose] noncomputable def burnsideI16h_eps : Matrix (Fin 2) (Fin 2) F →ₗ[K] (burnsideI16h_OI → K) where
  toFun X := Sum.elim (fun _ => burnsideI16h_c0 S (X 0 0))
    (Sum.elim (fun _ => burnsideI16h_c0 S (X 1 1))
      ![burnsideI16h_c0 S (X 0 1), burnsideI16h_c1 S (X 0 1)])
  map_add' X Y := by
    funext i
    rcases i with i | i | j
    · simp
    · simp
    · fin_cases j <;> simp
  map_smul' k X := by
    funext i
    rcases i with i | i | j
    · simp
    · simp
    · fin_cases j <;> simp

theorem burnsideI16h_eps_H (w : burnsideI16h_OI → K) :
    burnsideI16h_eps S (burnsideI16h_H S w) = w := by
  funext i
  rcases i with i | i | j
  · rw [burnsideI16h_fin1 i]
    simp [burnsideI16h_eps, burnsideI16h_H, burnsideI16h_hmat, burnsideI16h_c0_alg]
  · rw [burnsideI16h_fin1 i]
    simp [burnsideI16h_eps, burnsideI16h_H, burnsideI16h_hmat, burnsideI16h_c0_alg]
  · fin_cases j
    · simp [burnsideI16h_eps, burnsideI16h_H, burnsideI16h_hmat, burnsideI16h_zf,
        burnsideI16h_c0_coord]
    · simp [burnsideI16h_eps, burnsideI16h_H, burnsideI16h_hmat, burnsideI16h_zf,
        burnsideI16h_c1_coord]

theorem burnsideI16h_H_eps {X : Matrix (Fin 2) (Fin 2) F} (hX : X ∈ hermA S.n F) :
    burnsideI16h_H S (burnsideI16h_eps S X) = X := by
  have h00 := hermA_apply hX 0 0
  have h11 := hermA_apply hX 1 1
  have h10 := hermA_apply hX 1 0
  obtain ⟨k0, hk0⟩ := burnsideI16h_sig_fixed S.hK S.hn h00
  obtain ⟨k1, hk1⟩ := burnsideI16h_sig_fixed S.hK S.hn h11
  have hz : burnsideI16h_zf S (burnsideI16h_c0 S (X 0 1)) (burnsideI16h_c1 S (X 0 1)) = X 0 1 :=
    burnsideI16h_coord_spec S (X 0 1)
  ext i j
  fin_cases i <;> fin_cases j
  · simp [burnsideI16h_H, burnsideI16h_eps, burnsideI16h_hmat, ← hk0, burnsideI16h_c0_alg]
  · simpa [burnsideI16h_H, burnsideI16h_eps, burnsideI16h_hmat] using hz
  · simp [burnsideI16h_H, burnsideI16h_eps, burnsideI16h_hmat, hz, h10]
  · simp [burnsideI16h_H, burnsideI16h_eps, burnsideI16h_hmat, ← hk1, burnsideI16h_c0_alg]

@[expose] noncomputable def burnsideI16h_Tg (g : SL(2, F)) :
    Matrix (Fin 2) (Fin 2) F →ₗ[K] Matrix (Fin 2) (Fin 2) F :=
  (LinearMap.mulLeft K (g : Matrix (Fin 2) (Fin 2) F)).comp
    (LinearMap.mulRight K (frobPow S.n (g : Matrix (Fin 2) (Fin 2) F))ᵀ)

theorem burnsideI16h_Tg_apply (g : SL(2, F)) (X : Matrix (Fin 2) (Fin 2) F) :
    burnsideI16h_Tg S g X =
      (g : Matrix (Fin 2) (Fin 2) F) * X * (frobPow S.n (g : Matrix (Fin 2) (Fin 2) F))ᵀ := by
  simp [burnsideI16h_Tg, Matrix.mul_assoc]

theorem burnsideI16h_Tg_mem {X : Matrix (Fin 2) (Fin 2) F} (hX : X ∈ hermA S.n F) (g : SL(2, F)) :
    burnsideI16h_Tg S g X ∈ hermA S.n F := by
  rw [burnsideI16h_Tg_apply]
  exact twist_mem S.n (burnsideI16h_hσ S) hX _

theorem burnsideI16h_Tg_mul (g h : SL(2, F)) (X : Matrix (Fin 2) (Fin 2) F) :
    burnsideI16h_Tg S (g * h) X = burnsideI16h_Tg S g (burnsideI16h_Tg S h X) := by
  simp only [burnsideI16h_Tg_apply, Matrix.SpecialLinearGroup.coe_mul,
    JonesParshall.frobPow_mul, Matrix.transpose_mul, Matrix.mul_assoc]

theorem burnsideI16h_Tg_one (X : Matrix (Fin 2) (Fin 2) F) :
    burnsideI16h_Tg S (1 : SL(2, F)) X = X := by
  simp [burnsideI16h_Tg_apply, JonesParshall.frobPow_eq_map]

@[expose] noncomputable def burnsideI16h_L (g : SL(2, F)) :
    (burnsideI16h_OI → K) →ₗ[K] (burnsideI16h_OI → K) :=
  (burnsideI16h_eps S).comp ((burnsideI16h_Tg S g).comp (burnsideI16h_H S))

theorem burnsideI16h_H_L (g : SL(2, F)) (w : burnsideI16h_OI → K) :
    burnsideI16h_H S (burnsideI16h_L S g w) = burnsideI16h_Tg S g (burnsideI16h_H S w) :=
  burnsideI16h_H_eps S (burnsideI16h_Tg_mem S (burnsideI16h_H_mem S w) g)

theorem burnsideI16h_L_mul (g h : SL(2, F)) : burnsideI16h_L S (g * h) = burnsideI16h_L S g *
    burnsideI16h_L S h := by
  refine LinearMap.ext fun w => ?_
  change burnsideI16h_eps S (burnsideI16h_Tg S (g * h) (burnsideI16h_H S w)) =
    burnsideI16h_L S g (burnsideI16h_L S h w)
  rw [burnsideI16h_Tg_mul]
  change _ = burnsideI16h_eps S (burnsideI16h_Tg S g (burnsideI16h_H S (burnsideI16h_L S h w)))
  rw [burnsideI16h_H_L]

theorem burnsideI16h_L_one : burnsideI16h_L S (1 : SL(2, F)) = 1 := by
  refine LinearMap.ext fun w => ?_
  change burnsideI16h_eps S (burnsideI16h_Tg S 1 (burnsideI16h_H S w)) = w
  rw [burnsideI16h_Tg_one, burnsideI16h_eps_H]

@[expose] noncomputable def burnsideI16h_Lhom : SL(2, F) →* Module.End K (burnsideI16h_OI → K) where
  toFun := burnsideI16h_L S
  map_one' := burnsideI16h_L_one S
  map_mul' := burnsideI16h_L_mul S

@[expose] noncomputable def burnsideI16h_Θ :
    SL(2, F) →* ((burnsideI16h_OI → K) ≃ₗ[K] (burnsideI16h_OI → K)) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv K (burnsideI16h_OI → K)).toMonoidHom.comp
    (MonoidHom.toHomUnits (burnsideI16h_Lhom S))

theorem burnsideI16h_Θ_apply (g : SL(2, F)) (w : burnsideI16h_OI → K) :
    burnsideI16h_Θ S g w = burnsideI16h_L S g w := rfl

theorem burnsideI16h_Q_apply (w : burnsideI16h_OI → K) :
    CFSG.LieType.Universal.Spin.quadMinus 2 K S.b S.c w =
      w (Sum.inl 0) * w (Sum.inr (Sum.inl 0)) + w (Sum.inr (Sum.inr 0)) ^ 2 +
        S.b * w (Sum.inr (Sum.inr 0)) * w (Sum.inr (Sum.inr 1)) +
          S.c * w (Sum.inr (Sum.inr 1)) ^ 2 := by
  rw [CFSG.LieType.Universal.Spin.quadMinus_apply]
  congr 3
  exact Finset.sum_eq_single_of_mem 0 (Finset.mem_univ _)
    (fun b _ hb => absurd (burnsideI16h_fin1 b) hb)

theorem burnsideI16h_det_H (w : burnsideI16h_OI → K) :
    (burnsideI16h_H S w).det =
      algebraMap K F (CFSG.LieType.Universal.Spin.quadMinus 2 K S.b S.c w) := by
  rw [burnsideI16h_Q_apply, Matrix.det_fin_two]
  simp only [burnsideI16h_H, LinearMap.coe_mk, AddHom.coe_mk, burnsideI16h_hmat, of_apply,
    cons_val', cons_val_zero, cons_val_one, empty_val', cons_val_fin_one]
  have hn := burnsideI16h_norm_coord S (w (Sum.inr (Sum.inr 0))) (w (Sum.inr (Sum.inr 1)))
  unfold burnsideI16h_zf
  rw [hn, CharTwo.sub_eq_add]
  simp only [map_add, map_mul, map_pow]
  ring

theorem burnsideI16h_det_frob (g : SL(2, F)) :
    (frobPow S.n (g : Matrix (Fin 2) (Fin 2) F)).det = 1 := by
  rw [JonesParshall.frobPow_eq_map, ← RingHom.map_det, Matrix.SpecialLinearGroup.det_coe, map_one]

theorem burnsideI16h_Q_L (g : SL(2, F)) (w : burnsideI16h_OI → K) :
    CFSG.LieType.Universal.Spin.quadMinus 2 K S.b S.c (burnsideI16h_L S g w) =
      CFSG.LieType.Universal.Spin.quadMinus 2 K S.b S.c w := by
  apply (algebraMap K F).injective
  rw [← burnsideI16h_det_H, ← burnsideI16h_det_H, burnsideI16h_H_L, burnsideI16h_Tg_apply,
    Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, burnsideI16h_det_frob,
    Matrix.SpecialLinearGroup.det_coe, one_mul, mul_one]

theorem burnsideI16h_H_x : burnsideI16h_H S (Pi.single (Sum.inl 0) 1) =
    !![(1 : F), 0; 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [burnsideI16h_H, burnsideI16h_hmat, burnsideI16h_zf, Pi.single_apply]

theorem burnsideI16h_H_y : burnsideI16h_H S (Pi.single (Sum.inr (Sum.inl 0)) 1) =
    !![(0 : F), 0; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [burnsideI16h_H, burnsideI16h_hmat, burnsideI16h_zf, Pi.single_apply]

theorem burnsideI16h_H_u : burnsideI16h_H S (Pi.single (Sum.inr (Sum.inr 0)) 1) =
    !![(0 : F), 1; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [burnsideI16h_H, burnsideI16h_hmat, burnsideI16h_zf, Pi.single_apply]

theorem burnsideI16h_Θ_injective : Function.Injective (burnsideI16h_Θ S) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  have hg' : burnsideI16h_Θ S g = 1 := hg
  have key : ∀ w, (g : Matrix (Fin 2) (Fin 2) F) * burnsideI16h_H S w *
      (frobPow S.n (g : Matrix (Fin 2) (Fin 2) F))ᵀ = burnsideI16h_H S w := by
    intro w
    have h1 : burnsideI16h_L S g w = w := by
      have := congrArg (fun f => f w) hg'
      exact this
    have h2 := burnsideI16h_H_L S g w
    rw [h1, burnsideI16h_Tg_apply] at h2
    exact h2.symm
  have kx := key (Pi.single (Sum.inl 0) 1)
  have ky := key (Pi.single (Sum.inr (Sum.inl 0)) 1)
  have ku := key (Pi.single (Sum.inr (Sum.inr 0)) 1)
  rw [burnsideI16h_H_x] at kx
  rw [burnsideI16h_H_y] at ky
  rw [burnsideI16h_H_u] at ku
  have hinj : Function.Injective (sig (F := F) S.n) := RingHom.injective (sig (F := F) S.n)
  have hdet : (g : Matrix (Fin 2) (Fin 2) F).det = 1 := Matrix.SpecialLinearGroup.det_coe g
  rw [Matrix.det_fin_two] at hdet
  have x00 := congrFun (congrFun kx 0) 0
  have x01 := congrFun (congrFun kx 0) 1
  have y00 := congrFun (congrFun ky 0) 0
  have y11 := congrFun (congrFun ky 1) 1
  have u01 := congrFun (congrFun ku 0) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two, JonesParshall.frobPow_eq_map] at x00 x01 y00 y11 u01
  have h2c : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have hp0 : (g : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := fun h => by
    rw [h, zero_mul] at x00
    exact zero_ne_one x00
  have hs : (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := x01.resolve_left hp0
  rw [y00, hs] at u01 hdet
  simp only [zero_mul, zero_add, mul_zero, sub_zero] at u01 hdet
  have hσt : sig S.n ((g : Matrix (Fin 2) (Fin 2) F) 1 1) = (g : Matrix (Fin 2) (Fin 2) F) 1 1 :=
    mul_left_cancel₀ hp0 (u01.trans hdet.symm)
  rw [hσt] at y11
  have ht : (g : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := by
    have h2 : ((g : Matrix (Fin 2) (Fin 2) F) 1 1 + 1) ^ 2 = 0 := by
      linear_combination y11 + ((g : Matrix (Fin 2) (Fin 2) F) 1 1 + 1) * h2c
    exact CharTwo.add_eq_zero.1 (pow_eq_zero_iff (two_ne_zero) |>.1 h2)
  have hp : (g : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 := by
    rw [ht, mul_one] at hdet
    exact hdet
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hp, ht, y00, hs]

theorem burnsideI16h_comm_le_of_card {G : Type} [Group G] (O R : Subgroup G) [Finite O]
    (hRO : R ≤ O) (hcard : Nat.card O = 2 * Nat.card R) : ⁅O, O⁆ ≤ R := by
  classical
  set N : Subgroup O := R.subgroupOf O with hN
  have hNcard : Nat.card N = Nat.card R :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRO).toEquiv
  have hidx : N.index = 2 := by
    have h := Subgroup.card_mul_index N
    rw [hNcard, hcard] at h
    have hfin : Finite R :=
      Finite.of_injective (Subgroup.inclusion hRO) (Subgroup.inclusion_injective hRO)
    have hpos : 0 < Nat.card R := Nat.card_pos
    exact (Nat.eq_of_mul_eq_mul_left hpos (by rw [h]; ring))
  haveI : N.Normal := Subgroup.normal_of_index_eq_two hidx
  have hQcard : Nat.card (O ⧸ N) = 2 := by rw [← Subgroup.index_eq_card, hidx]
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : IsCyclic (O ⧸ N) := isCyclic_of_prime_card hQcard
  letI : CommGroup (O ⧸ N) := IsCyclic.commGroup
  rw [Subgroup.commutator_le]
  intro x hx y hy
  have : ((⟨x, hx⟩ : O) * ⟨y, hy⟩ * (⟨x, hx⟩ : O)⁻¹ * (⟨y, hy⟩ : O)⁻¹) ∈ N := by
    rw [← QuotientGroup.eq_one_iff]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [mul_comm (QuotientGroup.mk (⟨x, hx⟩ : O) : O ⧸ N) (QuotientGroup.mk (⟨y, hy⟩ : O))]
    group
  rw [commutatorElement_def]
  exact this

theorem burnsideI16h_omega_ne (k : K) : algebraMap K F k ≠ S.ω := by
  intro h
  apply S.hirr k
  apply (algebraMap K F).injective
  rw [map_zero, map_add, map_add, map_mul, map_pow, h]
  exact S.hω

include S in
theorem burnsideI16h_perfect : commutator SL(2, F) = ⊤ := by
  have h2c : (2 : F) = 0 := CharP.cast_eq_zero F 2
  refine Matrix.SL2.commutator_eq_top (a := S.ω) ?_ ?_
  · intro h
    exact burnsideI16h_omega_ne S 0 (by rw [map_zero, h])
  · intro h
    have h' : (S.ω + 1) ^ 2 = 0 := by linear_combination h + (S.ω + 1) * h2c
    have h'' : S.ω = 1 := CharTwo.add_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h')
    exact burnsideI16h_omega_ne S 1 (by rw [map_one, h''])

noncomputable abbrev burnsideI16h_O : Subgroup ((burnsideI16h_OI → K) ≃ₗ[K] (burnsideI16h_OI → K)) :=
  TauCeti.QuadraticMap.orthogonalGroup (CFSG.LieType.Universal.Spin.quadMinus 2 K S.b S.c)

theorem burnsideI16h_finite_linEquiv : Finite ((burnsideI16h_OI → K) ≃ₗ[K] (burnsideI16h_OI → K)) :=
  Finite.of_injective (fun g : (burnsideI16h_OI → K) ≃ₗ[K] (burnsideI16h_OI → K) =>
    (g : (burnsideI16h_OI → K) → (burnsideI16h_OI → K))) DFunLike.coe_injective

theorem burnsideI16h_range_le : (burnsideI16h_Θ S).range ≤ burnsideI16h_O S := by
  rintro _ ⟨g, rfl⟩
  exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun w => burnsideI16h_Q_L S g w

theorem burnsideI16h_card_O :
    Nat.card (burnsideI16h_O S) = 2 * Nat.card SL(2, F) := by
  haveI : Finite K := Finite.of_fintype K
  haveI : Finite F := Finite.of_fintype F
  have hO : (Nat.card (burnsideI16h_O S) : ℤ) =
      2 * (Nat.card K : ℤ) ^ (1 * (1 + 1)) * ((Nat.card K : ℤ) ^ (1 + 1) + 1) *
        ∏ i ∈ Finset.Icc 1 1, (((Nat.card K : ℤ) ^ 2) ^ i - 1) :=
    CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_quadMinus (K := K) S.hirr 1
  have hSL : Nat.card SL(2, F) = Nat.card F * (Nat.card F ^ 2 - 1) := by
    rw [← CFSG.Open.StatedAPI.card_statedSL, CFSG.Open.StatedAPI.card_statedSL_two]
  have hF : Nat.card F = Nat.card K ^ 2 := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, burnsideI16h_hF S, S.hK, ← pow_mul,
      mul_comm]
  have hq : 2 ≤ Nat.card K := Finite.one_lt_card
  have h1 : 1 ≤ (Nat.card K ^ 2) ^ 2 := Nat.one_le_pow _ _ (by positivity)
  rw [hSL, hF]
  zify [h1]
  rw [hO]
  simp only [Finset.Icc_self, Finset.prod_singleton]
  push_cast
  ring

end Hermitian

section Converse

open CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Assembly.LowTwoRank Matrix


end Converse

section Final

open CFSG.Quasithin CFSG.Quasithin.JonesParshall Matrix CFSG.ClassicalGroups.Orthogonal

variable {K F : Type} [Field K] [Fintype K] [CharP K 2] [Field F] [Fintype F] [Algebra K F]
  [CharP F 2] (S : burnsideI16h_Setup K F)

theorem burnsideI16h_range_eq :
    (burnsideI16h_Θ S).range = ⁅burnsideI16h_O S, burnsideI16h_O S⁆ := by
  haveI := burnsideI16h_finite_linEquiv (K := K)
  have hinj := burnsideI16h_Θ_injective S
  apply le_antisymm
  · have h1 : (burnsideI16h_Θ S).range =
        Subgroup.map (burnsideI16h_Θ S) ⁅(⊤ : Subgroup SL(2, F)), ⊤⁆ := by
      rw [← commutator_def, burnsideI16h_perfect S, ← MonoidHom.range_eq_map]
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map] at h1
    calc (burnsideI16h_Θ S).range
        = ⁅(burnsideI16h_Θ S).range, (burnsideI16h_Θ S).range⁆ := h1
      _ ≤ _ := Subgroup.commutator_mono (burnsideI16h_range_le S) (burnsideI16h_range_le S)
  · apply burnsideI16h_comm_le_of_card _ _ (burnsideI16h_range_le S)
    rw [burnsideI16h_card_O, Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm]

@[expose] noncomputable def burnsideI16h_ΘEquiv :
    SL(2, F) ≃* ↥⁅burnsideI16h_O S, burnsideI16h_O S⁆ :=
  (MonoidHom.ofInjective (burnsideI16h_Θ_injective S)).trans
    (MulEquiv.subgroupCongr (burnsideI16h_range_eq S))

@[expose] noncomputable def burnsideI16h_gammaEquiv :
    StatedOmega (StatedQuadMinus 2 K S.b S.c) ≃* ↥⁅burnsideI16h_O S, burnsideI16h_O S⁆ :=
  ((toLinEquiv burnsideI16h_OI K).subgroupMap (StatedOmega (StatedQuadMinus 2 K S.b S.c))).trans
    (MulEquiv.subgroupCongr (by
      rw [statedOmega_eq_comap (CFSG.LieType.Universal.Spin.coe_quadMinus 2 K S.b S.c)]
      exact Subgroup.map_comap_eq_self_of_surjective (toLinEquiv burnsideI16h_OI K).surjective _))

@[expose] noncomputable def burnsideI16h_β : (burnsideI16h_OI → K) ≃+ ↥(hermA S.n F) where
  toFun w := ⟨burnsideI16h_H S w, burnsideI16h_H_mem S w⟩
  invFun X := burnsideI16h_eps S (X : Matrix (Fin 2) (Fin 2) F)
  left_inv w := burnsideI16h_eps_H S w
  right_inv X := Subtype.ext (burnsideI16h_H_eps S X.2)
  map_add' w w' := Subtype.ext (map_add (burnsideI16h_H S) w w')

theorem burnsideI16h_β_Θ (g : SL(2, F)) (w : burnsideI16h_OI → K) :
    burnsideI16h_β S (burnsideI16h_Θ S g w) =
      hermAct S.n (burnsideI16h_hσ S) g (burnsideI16h_β S w) := by
  apply Subtype.ext
  rw [hermAct_coe]
  change burnsideI16h_H S (burnsideI16h_L S g w) = _
  rw [burnsideI16h_H_L, burnsideI16h_Tg_apply]
  rfl

@[expose] noncomputable def burnsideI16h_θ :
    StatedOmega (StatedQuadMinus 2 K S.b S.c) ≃* SL(2, F) :=
  (burnsideI16h_gammaEquiv S).trans (burnsideI16h_ΘEquiv S).symm


end Final

section JPHelpers3


end JPHelpers3


section


end

end CFSG.ASVolI
