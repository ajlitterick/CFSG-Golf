module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.ModelCheckS
import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.ModelCheckAut
import all CFSG.Fischer.F4

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG.Fischer CFSG.ClassicalGroups.UnitaryFlag
open scoped commutatorElement

theorem lower_of_mem_normalizer_Ssub {s : SU52} (hs : s ∈ normalizer (Ssub : Set SU52)) :
    ∀ i j : Fin 5, i < j → mat s i j = 0 := by
  have hρ : ρ s ∈ normalizer (hypUnitriangular hF4 2 1 : Set (hypSU hF4 2 1)) := by
    refine mem_normalizer_iff.2 fun u => ?_
    obtain ⟨g, rfl⟩ := ρ.surjective u
    rw [← map_inv, ← map_mul, ← map_mul, ← mem_Ssub_iff_ρ, ← mem_Ssub_iff_ρ]
    exact mem_normalizer_iff.1 hs g
  rw [CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.normalizer_hypUnitriangular hF4
    (by norm_num) (by norm_num)] at hρ
  have hT := (mem_hypBorel_iff_blockTriangular hF4 (by norm_num) (ρ s)).1 hρ
  intro i j hij
  rw [← mat_ρ_apply]
  exact hT ((fullPos_yIdx_lt_iff i j).2 hij)

theorem DiagSub_le_normalizer_Ssub : DiagSub ≤ normalizer (Ssub : Set SU52) := by
  rintro g ⟨α, β, γ, hα, hβ, hγ, hgm⟩
  have hd : ∀ i, (![α, β, γ, β, α] : Fin 5 → F4) i ≠ 0 := by
    intro i
    fin_cases i <;> simpa
  refine mem_normalizer_fintype fun x hx => ?_
  obtain ⟨h1, h2⟩ := mem_Ssub.1 hx
  exact mem_Ssub.2 ⟨fun i j hij => by rw [mat_conj_diag hd hgm, h1 i j hij, mul_zero, zero_mul],
    fun i => by rw [mat_conj_diag hd hgm, h2 i, mul_one, mul_inv_cancel₀ (hd i)]⟩

theorem Esub_le_normalizer_Ssub : Esub ≤ normalizer (Ssub : Set SU52) :=
  Esub_le_DiagSub.trans DiagSub_le_normalizer_Ssub

theorem e₂SU_mem_normalizer_Ssub : e₂SU ∈ normalizer (Ssub : Set SU52) :=
  Esub_le_normalizer_Ssub (mem_sup_right (mem_zpowers _))

theorem mat_npow (g : SU52) (n : ℕ) : mat (g ^ n) = mat g ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, mat_one]
  | succ n ih => rw [pow_succ, pow_succ, mat_mul, ih]

@[expose] def eTorDiag (i j : Fin 3) : Fin 5 → F4 := fun k =>
  (![1, F4.ω, F4.ω, F4.ω, 1] : Fin 5 → F4) k ^ (i : ℕ) *
    (![F4.ω, F4.ω, bar F4.ω, F4.ω, F4.ω] : Fin 5 → F4) k ^ (j : ℕ)

theorem mat_eTor (i j : Fin 3) :
    mat (e₁SU ^ (i : ℕ) * e₂SU ^ (j : ℕ)) = Matrix.diagonal (eTorDiag i j) := by
  rw [mat_mul, mat_npow, mat_npow, mat_e₁SU, mat_e₂SU, e₁Mat, e₂Mat, Matrix.diagonal_pow,
    Matrix.diagonal_pow, Matrix.diagonal_mul_diagonal]
  rfl


theorem eTorDiag_ne_zero : ∀ i j k, eTorDiag i j k ≠ 0 := by
  unfold eTorDiag
  simp only [bar_apply]
  decide

theorem exists_eTorDiag : ∀ a b c d e : F4, bar a * e = 1 → bar b * d = 1 → bar c * c = 1 →
    a * b * c * d * e = 1 → ∃ i j : Fin 3, eTorDiag i j = ![a, b, c, d, e] := by
  unfold eTorDiag
  simp only [bar_apply]
  decide

theorem inv_mul_mem_Ssub_of_diag {t s : SU52} {d : Fin 5 → F4}
    (ht : mat t = Matrix.diagonal d) (hd0 : ∀ i, d i ≠ 0)
    (hs : ∀ i j : Fin 5, i < j → mat s i j = 0) (hd : ∀ i, mat s i i = d i) :
    t⁻¹ * s ∈ Ssub := by
  have hinv : mat t⁻¹ = Matrix.diagonal fun i => (d i)⁻¹ := mat_inv_eq (by
    rw [ht, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact mul_inv_cancel₀ (hd0 i))
  refine mem_Ssub.2 ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [mat_mul, hinv, Matrix.diagonal_mul, hs i j hij, mul_zero]
  · rw [mat_mul, hinv, Matrix.diagonal_mul, hd i, inv_mul_cancel₀ (hd0 i)]

theorem diag_facts_of_lower {s : SU52} (hs : ∀ i j : Fin 5, i < j → mat s i j = 0) :
    bar (mat s 0 0) * mat s 4 4 = 1 ∧ bar (mat s 1 1) * mat s 3 3 = 1 ∧
      bar (mat s 2 2) * mat s 2 2 = 1 ∧
      mat s 0 0 * mat s 1 1 * mat s 2 2 * mat s 3 3 * mat s 4 4 = 1 := by
  obtain ⟨hU, hdet⟩ := mem_SU52.1 s.2
  have u01 := hs 0 1 (by decide)
  have u02 := hs 0 2 (by decide)
  have u03 := hs 0 3 (by decide)
  have u04 := hs 0 4 (by decide)
  have u12 := hs 1 2 (by decide)
  have u13 := hs 1 3 (by decide)
  have u14 := hs 1 4 (by decide)
  have u23 := hs 2 3 (by decide)
  have u24 := hs 2 4 (by decide)
  have u34 := hs 3 4 (by decide)
  have e04 := congrFun (congrFun hU 0) 4
  have e13 := congrFun (congrFun hU 1) 3
  have e22 := congrFun (congrFun hU 2) 2
  simp [Matrix.mul_apply, Fin.sum_univ_five, J5, u01, u02, u03, u04, u12, u13, u14, u23, u24,
    u34] at e04 e13 e22
  have hlt : (mat s).IsLowerTriangular := fun i j hij =>
    hs i j (OrderDual.toDual_lt_toDual.1 hij)
  have hdet' := Matrix.det_of_isLowerTriangular (mat s) hlt
  rw [hdet, Fin.prod_univ_five] at hdet'
  exact ⟨e04, e13, e22, hdet'.symm⟩

theorem exists_mul_of_mem_normalizer_Ssub {n : SU52} (hn : n ∈ normalizer (Ssub : Set SU52)) :
    ∃ i j : Fin 3, (e₁SU ^ (i : ℕ) * e₂SU ^ (j : ℕ))⁻¹ * n ∈ Ssub ∧
      ∀ k, mat n k k = eTorDiag i j k := by
  have hlow := lower_of_mem_normalizer_Ssub hn
  obtain ⟨h04, h13, h22, hdet⟩ := diag_facts_of_lower hlow
  obtain ⟨i, j, hij⟩ := exists_eTorDiag _ _ _ _ _ h04 h13 h22 hdet
  have hd : ∀ k, mat n k k = eTorDiag i j k := fun k => by
    rw [hij]
    fin_cases k <;> rfl
  exact ⟨i, j, inv_mul_mem_Ssub_of_diag (mat_eTor i j) (eTorDiag_ne_zero i j) hlow hd, hd⟩


theorem normalizer_Ssub_conj_mem_commutator {n x : SU52}
    (hn : n ∈ normalizer (Ssub : Set SU52)) (hx : x ∈ ⁅Ssub, Ssub⁆) :
    n * x * n⁻¹ ∈ ⁅Ssub, Ssub⁆ := by
  have hle : ⁅Ssub, Ssub⁆ ≤ (⁅Ssub, Ssub⁆ : Subgroup SU52).comap (MulAut.conj n).toMonoidHom := by
    rw [commutator_le]
    intro g hg h hh
    change n * ⁅g, h⁆ * n⁻¹ ∈ ⁅Ssub, Ssub⁆
    rw [show n * ⁅g, h⁆ * n⁻¹ = ⁅n * g * n⁻¹, n * h * n⁻¹⁆ by
      simp only [commutatorElement_def]
      group]
    exact commutator_mem_commutator ((mem_normalizer_iff.1 hn g).1 hg)
      ((mem_normalizer_iff.1 hn h).1 hh)
  exact hle hx


theorem mem_X₄sub_sup_Fsub_iff_mat {x : SU52} :
    x ∈ X₄sub ⊔ Fsub ↔ x ∈ Ssub ∧ mat x 2 1 = 0 ∧ mat x 1 0 = 0 := by
  rw [← commutator_Ssub_eq_X₄sub_sup_Fsub, commutator_Ssub, mem_ZX₁sub_sup_X₃sub_sup_X₄sub_iff]


theorem mat_conj_e₂_two_zero (x : SU52) : mat (e₂SU * x * e₂SU⁻¹) 2 0 = F4.ω * mat x 2 0 := by
  have hd : ∀ i, (![F4.ω, F4.ω, bar F4.ω, F4.ω, F4.ω] : Fin 5 → F4) i ≠ 0 := by
    intro i
    fin_cases i <;> simp only [bar_apply] <;> decide
  rw [mat_conj_diag hd (by rw [mat_e₂SU, e₂Mat])]
  change bar F4.ω * mat x 2 0 * F4.ω⁻¹ = F4.ω * mat x 2 0
  have h : bar F4.ω * F4.ω⁻¹ = F4.ω := by
    rw [bar_apply]
    decide
  linear_combination mat x 2 0 * h


theorem eq_Ssub_of_isPGroup {Q : Subgroup SU52} (hQ : IsPGroup 2 Q) (hSQ : Ssub ≤ Q) :
    Q = Ssub := by
  obtain ⟨P, hP⟩ := exists_sylow_Ssub
  rw [← hP] at hSQ ⊢
  exact P.is_maximal' hQ hSQ

theorem mat_mul_self_of_lower {s t : SU52} (hs : ∀ i j : Fin 5, i < j → mat s i j = 0)
    (ht : ∀ i j : Fin 5, i < j → mat t i j = 0) (k : Fin 5) :
    mat (s * t) k k = mat s k k * mat t k k := by
  rw [mat_mul, Matrix.mul_apply, Finset.sum_eq_single k]
  · intro l _ hl
    rcases lt_or_gt_of_ne hl with h | h
    · rw [ht l k h, mul_zero]
    · rw [hs k l h, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ k) h

theorem exists_eq_conj_of_mem_of_isPGroup {Q : Subgroup (MulAut SU52)} (hQ : IsPGroup 2 Q)
    (hQS : ∀ α ∈ Q, ∀ x ∈ Ssub, α x ∈ Ssub)
    (he : ∀ α ∈ Q, MulAut.conj e₁SU * α * (MulAut.conj e₁SU)⁻¹ ∈ Q)
    {α : MulAut SU52} (hα : α ∈ Q) : ∃ s ∈ Ssub, α = MulAut.conj s := by
  have inner : ∀ n : SU52, MulAut.conj n ∈ Q → n ∈ Ssub := by
    intro n hn
    have hnN : n ∈ normalizer (Ssub : Set SU52) :=
      mem_normalizer_fintype fun x hx => hQS _ hn x hx
    obtain ⟨k, hk⟩ := hQ ⟨_, hn⟩
    have h1 : (MulAut.conj n) ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have hk' : n ^ 2 ^ k = 1 := (conj_eq_one_iff _).1 (by rw [map_pow, h1])
    have hZ : IsPGroup 2 (zpowers n) := IsPGroup.of_card_dvd_pow (n := k) (by
      rw [Nat.card_zpowers]
      exact orderOf_dvd_of_pow_eq_one hk')
    have hsup := (IsPGroup.of_card card_Ssub).to_sup_of_normal_left' hZ (zpowers_le.2 hnN)
    rw [← eq_Ssub_of_isPGroup hsup le_sup_left]
    exact mem_sup_right (mem_zpowers n)
  obtain ⟨n, rfl | rfl⟩ := exists_eq_conj_or_eq_conj_mul_fld α
  · exact ⟨n, inner n hα, rfl⟩
  exfalso
  have hnN : n ∈ normalizer (Ssub : Set SU52) := mem_normalizer_fintype fun x hx => by
    have := hQS _ hα (fld x) (fld_mem_Ssub hx)
    simpa [MulAut.mul_apply, MulAut.conj_apply, fld_fld] using this
  have hγ : MulAut.conj e₁SU * (MulAut.conj n * fld) * (MulAut.conj e₁SU)⁻¹ *
      (MulAut.conj n * fld)⁻¹ = MulAut.conj (e₁SU * n * e₁SU * n⁻¹) := by
    rw [mul_inv_rev, fld_inv]
    refine MulEquiv.ext fun g => ?_
    simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_inv_apply, map_mul, map_inv,
      fld_fld, fld_e₁SU, inv_inv]
  have hm := inner _ (by
    rw [← hγ]
    exact mul_mem (he _ hα) (inv_mem hα))
  have he₁N : e₁SU ∈ normalizer (Ssub : Set SU52) :=
    Esub_le_normalizer_Ssub (mem_sup_left (mem_zpowers _))
  have l1 := lower_of_mem_normalizer_Ssub he₁N
  have l2 := lower_of_mem_normalizer_Ssub hnN
  have l3 := lower_of_mem_normalizer_Ssub (mul_mem he₁N hnN)
  have l4 := lower_of_mem_normalizer_Ssub (mul_mem (mul_mem he₁N hnN) he₁N)
  have l5 := lower_of_mem_normalizer_Ssub (inv_mem hnN)
  have d := (mem_Ssub.1 hm).2 1
  rw [mat_mul_self_of_lower l4 l5, mat_mul_self_of_lower l3 l1, mat_mul_self_of_lower l1 l2,
    mat_e₁SU, e₁Mat, Matrix.diagonal_apply_eq] at d
  have dn : mat n 1 1 * mat n⁻¹ 1 1 = 1 := by
    rw [← mat_mul_self_of_lower l2 l5, mul_inv_cancel, mat_one, Matrix.one_apply_eq]
  change F4.ω * mat n 1 1 * F4.ω * mat n⁻¹ 1 1 = 1 at d
  have h : F4.ω * F4.ω = 1 := by linear_combination d - F4.ω * F4.ω * dn
  exact absurd h (by decide)

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
