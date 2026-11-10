module

public import CFSG.Milestones.ASVolI.A3Aut.Util
public import CFSG.Milestones.ASVolI.A2OddAut

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.GorensteinWalter CFSG.RankThree.PartTwo.KFacts
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open scoped MatrixGroups

section L2Model

variable {K : Type} [Field K]

@[expose] noncomputable def burnsideAut_sl2DiagHom (K : Type) [Field K] : Kˣ →* SL(2, K) where
  toFun l := ⟨!![(l : K), 0; 0, ((l⁻¹ : Kˣ) : K)], by simp [Matrix.det_fin_two_of]⟩
  map_one' := by
    apply Subtype.ext
    change (!![((1 : Kˣ) : K), 0; 0, ((1⁻¹ : Kˣ) : K)] : Matrix (Fin 2) (Fin 2) K) = 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' l m := by
    apply Subtype.ext
    change (!![((l * m : Kˣ) : K), 0; 0, (((l * m)⁻¹ : Kˣ) : K)] : Matrix (Fin 2) (Fin 2) K) =
      !![(l : K), 0; 0, ((l⁻¹ : Kˣ) : K)] * !![(m : K), 0; 0, ((m⁻¹ : Kˣ) : K)]
    rw [Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [mul_comm]

@[expose] noncomputable def burnsideAut_psl2Diag (K : Type) [Field K] : Subgroup (PSL2 K) :=
  ((psl2QuotientMap K).comp (burnsideAut_sl2DiagHom K)).range

theorem burnsideAut_card_psl2Diag_dvd [Finite K] :
    Nat.card (burnsideAut_psl2Diag K) ∣ Nat.card Kˣ :=
  Subgroup.card_range_dvd _

theorem burnsideAut_card_psl2Diag_odd [Finite K] {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n) :
    Odd (Nat.card (burnsideAut_psl2Diag K)) := by
  classical
  refine Odd.of_dvd_nat ?_ burnsideAut_card_psl2Diag_dvd
  haveI : Fintype K := Fintype.ofFinite K
  rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, hK]
  have h2 : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have he : Even (2 ^ n) := (Nat.even_pow' (by omega)).2 even_two
  obtain ⟨k, hk⟩ := he
  exact ⟨k - 1, by omega⟩

theorem burnsideAut_psl2Diag_le_borel : burnsideAut_psl2Diag K ≤ psl2Borel K := by
  rintro _ ⟨l, rfl⟩
  rw [psl2Borel_eq_map]
  refine ⟨burnsideAut_sl2DiagHom K l, ?_, rfl⟩
  exact (sl2_mem_stabilizer_infinity_iff _).2 rfl

theorem burnsideAut_psl2Upper_eq_map :
    psl2UpperUnipotentSubgroup K = (sl2UpperUnipotentSubgroup K).map (psl2QuotientMap K) := by
  rw [psl2UpperUnipotentSubgroup, psl2UpperUnipotentHom, MonoidHom.range_comp]
  rfl

theorem burnsideAut_psl2Borel_eq_sup :
    psl2Borel K = psl2UpperUnipotentSubgroup K ⊔ burnsideAut_psl2Diag K := by
  refine le_antisymm ?_ (sup_le psl2UpperUnipotent_le_borel burnsideAut_psl2Diag_le_borel)
  rw [psl2Borel_eq_map]
  rintro _ ⟨A, hA, rfl⟩
  have h10 : A.val 1 0 = 0 := (sl2_mem_stabilizer_infinity_iff A).1 hA
  have hdet : A.val 0 0 * A.val 1 1 = 1 := by
    have h := A.property
    rw [Matrix.det_fin_two, h10] at h
    simpa using h
  have ha : A.val 0 0 ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hdet
    exact zero_ne_one hdet
  set a : Kˣ := Units.mk0 (A.val 0 0) ha with haDef
  have hinv : ((a⁻¹ : Kˣ) : K) = A.val 1 1 := by
    rw [Units.val_inv_eq_inv_val, haDef, Units.val_mk0]
    exact inv_eq_of_mul_eq_one_right hdet
  have hAeq : A = sl2UpperUnipotent (A.val 0 1 * A.val 0 0) * burnsideAut_sl2DiagHom K a := by
    apply Subtype.ext
    change A.val = (!![1, A.val 0 1 * A.val 0 0; 0, 1] : Matrix (Fin 2) (Fin 2) K) *
      !![(a : K), 0; 0, ((a⁻¹ : Kˣ) : K)]
    rw [Matrix.mul_fin_two, hinv]
    ext i j
    fin_cases i <;> fin_cases j
    · simp [haDef]
    · have h3 : A.val 0 1 * A.val 0 0 * A.val 1 1 = A.val 0 1 := by rw [mul_assoc, hdet, mul_one]
      simp [h3]
    · simp [h10]
    · simp
  rw [hAeq, map_mul]
  refine Subgroup.mul_mem_sup ?_ ⟨a, rfl⟩
  rw [burnsideAut_psl2Upper_eq_map]
  exact ⟨_, ⟨Multiplicative.ofAdd _, rfl⟩, rfl⟩

theorem burnsideAut_psl2FieldAut_upper (σ : K ≃+* K) (x : K) :
    psl2FieldAut K σ (psl2QuotientMap K (sl2UpperUnipotent x)) =
      psl2QuotientMap K (sl2UpperUnipotent (σ x)) := by
  rw [psl2FieldAut_apply]
  change psl2RingEquiv σ (QuotientGroup.mk' _ _) = QuotientGroup.mk' _ _
  rw [psl2RingEquiv_mk]
  congr 1
  apply Subtype.ext
  show Matrix.map (!![1, x; 0, 1] : Matrix (Fin 2) (Fin 2) K) σ.toRingHom = !![1, σ x; 0, 1]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem burnsideAut_psl2FieldAut_diag (σ : K ≃+* K) (l : Kˣ) :
    psl2FieldAut K σ (psl2QuotientMap K (burnsideAut_sl2DiagHom K l)) =
      psl2QuotientMap K (burnsideAut_sl2DiagHom K (Units.map (σ : K →* K) l)) := by
  rw [psl2FieldAut_apply]
  change psl2RingEquiv σ (QuotientGroup.mk' _ _) = QuotientGroup.mk' _ _
  rw [psl2RingEquiv_mk]
  congr 1
  apply Subtype.ext
  show Matrix.map (!![(l : K), 0; 0, ((l⁻¹ : Kˣ) : K)] : Matrix (Fin 2) (Fin 2) K) σ.toRingHom =
    !![((Units.map (σ : K →* K) l : Kˣ) : K), 0; 0, (((Units.map (σ : K →* K) l)⁻¹ : Kˣ) : K)]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem burnsideAut_map_psl2FieldAut_upper [Finite K] (σ : K ≃+* K) :
    (psl2UpperUnipotentSubgroup K).map (psl2FieldAut K σ).toMonoidHom =
      psl2UpperUnipotentSubgroup K := by
  have hle : ∀ τ : K ≃+* K, (psl2UpperUnipotentSubgroup K).map (psl2FieldAut K τ).toMonoidHom ≤
      psl2UpperUnipotentSubgroup K := by
    intro τ
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨x, rfl⟩ := (mem_psl2UpperUnipotentSubgroup_iff y).1 hy
    rw [mem_psl2UpperUnipotentSubgroup_iff]
    exact ⟨τ x, burnsideAut_psl2FieldAut_upper τ x⟩
  refine Subgroup.eq_of_le_of_card_ge (hle σ) ?_
  rw [Subgroup.card_map_of_injective (psl2FieldAut K σ).injective]

theorem burnsideAut_map_psl2FieldAut_diag [Finite K] (σ : K ≃+* K) :
    (burnsideAut_psl2Diag K).map (psl2FieldAut K σ).toMonoidHom = burnsideAut_psl2Diag K := by
  have hle : ∀ τ : K ≃+* K, (burnsideAut_psl2Diag K).map (psl2FieldAut K τ).toMonoidHom ≤
      burnsideAut_psl2Diag K := by
    intro τ
    rintro _ ⟨_, ⟨l, rfl⟩, rfl⟩
    exact ⟨Units.map (τ : K →* K) l, (burnsideAut_psl2FieldAut_diag τ l).symm⟩
  refine Subgroup.eq_of_le_of_card_ge (hle σ) ?_
  rw [Subgroup.card_map_of_injective (psl2FieldAut K σ).injective]

end L2Model

section InnGeneral

theorem burnsideAut_inn_normal (S : Type*) [Group S] :
    (MulAut.conj : S →* MulAut S).range.Normal :=
  ⟨fun _ ⟨y, hy⟩ χ => ⟨χ y, by rw [← hy, burnsideAut_mul_conj_mul_inv]⟩⟩

theorem burnsideAut_map_conj_map_conj {S : Type*} [Group S] (U : Subgroup S) (φ : MulAut S) :
    (U.map (MulAut.conj : S →* MulAut S)).map (MulAut.conj φ).toMonoidHom =
      (U.map φ.toMonoidHom).map (MulAut.conj : S →* MulAut S) := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext y : 1
  exact burnsideAut_mul_conj_mul_inv φ y

theorem burnsideAut_mem_normalizer_map_conj {S : Type*} [Group S] {U : Subgroup S} {φ : MulAut S}
    (hφ : U.map φ.toMonoidHom = U) :
    φ ∈ Subgroup.normalizer ((U.map (MulAut.conj : S →* MulAut S) : Subgroup (MulAut S)) :
      Set (MulAut S)) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  change Subgroup.map (MulAut.conj φ).toMonoidHom _ = _
  rw [burnsideAut_map_conj_map_conj, hφ]

theorem burnsideAut_conj_injective {S : Type*} [Group S] (hZ : Subgroup.center S = ⊥) :
    Function.Injective (MulAut.conj : S →* MulAut S) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← hZ]
  intro y hy
  rw [Subgroup.mem_center_iff]
  intro x
  have h1 := congrArg (fun φ : MulAut S => φ x) (MonoidHom.mem_ker.1 hy)
  simp only [MulAut.conj_apply, MulAut.one_apply] at h1
  calc x * y = y * x * y⁻¹ * y := by rw [h1]
    _ = y * x := by group


end InnGeneral

section L2Family

open CFSG.Assembly.LowTwoRank

variable {K : Type} [Field K] [Finite K]

theorem burnsideAut_psl2_inn_inf_field :
    (MulAut.conj : PSL2 K →* MulAut (PSL2 K)).range ⊓ (psl2FieldAut K).range = ⊥ := by
  rw [eq_bot_iff]
  rintro φ ⟨hφI, hφΦ⟩
  exact (stdPinnedPSL2_separated (K := K)).field_inter φ hφΦ (innAut_le_range_pglAction K hφI)

theorem burnsideAut_psl2_aut_mem [CharP K 2] (α : MulAut (PSL2 K)) :
    α ∈ (MulAut.conj : PSL2 K →* MulAut (PSL2 K)).range ⊔ (psl2FieldAut K).range := by
  obtain ⟨g, σ, rfl⟩ := CFSG.RankThree.PartTwo.KFacts.exists_pglAction_mul_psl2FieldAut α
  obtain ⟨x, rfl⟩ := CFSG.SignalizerFunctorTheorem.McBride.PSL2Even.toPGL_surjective K g
  rw [pglAction_toPGL]
  exact Subgroup.mul_mem_sup ⟨x, rfl⟩ ⟨σ, rfl⟩


end L2Family

end CFSG.ASVolI
