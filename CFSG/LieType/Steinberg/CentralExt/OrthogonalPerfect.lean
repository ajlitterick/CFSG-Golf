module

public import CFSG.LieType.Steinberg.CentralExt.Model
public import CFSG.LieType.Steinberg.CentralExt.Families
public import CFSG.LieType.Steinberg.CentralExt.SpinMinus
public import CFSG.LieType.Steinberg.CentralExt.PerfectCover

public section

namespace CFSG.LieType.Steinberg

open CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal.Spin
  CFSG.ClassicalGroups.Orthogonal
open scoped Matrix

section Omega

variable {σ : Type} [Fintype σ] [DecidableEq σ] {K : Type} [Field K] {Q₀ : (σ → K) → K}

theorem preserves_of_mem_statedOmega {A : GL σ K} (hA : A ∈ StatedOmega Q₀) (v : σ → K) :
    Q₀ ((A : Matrix σ σ K) *ᵥ v) = Q₀ v := by
  set H := Subgroup.closure {A : GL σ K | ∀ v, Q₀ ((A : Matrix σ σ K) *ᵥ v) = Q₀ v}
  have hle : StatedOmega Q₀ ≤ H := Subgroup.commutator_le.2 fun a ha b hb => by
    rw [commutatorElement_def]
    exact H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)
  have key : ∀ B ∈ H, ∀ v, Q₀ ((B : Matrix σ σ K) *ᵥ v) = Q₀ v := by
    intro B hB
    induction hB using Subgroup.closure_induction with
    | mem B hB => exact hB
    | one => simp
    | mul B C _ _ hB hC =>
      intro v
      rw [Units.val_mul, ← Matrix.mulVec_mulVec, hB, hC]
    | inv B _ hB =>
      intro v
      have h := hB ((B⁻¹ : GL σ K) *ᵥ v)
      rwa [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.one_mulVec, eq_comm] at h
  exact key A (hle hA) v

theorem sq_eq_one_of_scalar_mem_statedOmega {Q : QuadraticForm K (σ → K)} (hQ₀ : ⇑Q = Q₀)
    (hv : ∃ v, Q v ≠ 0) {c : Kˣ} (hc : Matrix.GeneralLinearGroup.scalar σ c ∈ StatedOmega Q₀) :
    (c : K) ^ 2 = 1 := by
  obtain ⟨v, hv⟩ := hv
  have h := preserves_of_mem_statedOmega hc v
  have hmul : ((Matrix.GeneralLinearGroup.scalar σ c : GL σ K) : Matrix σ σ K) *ᵥ v =
      (c : K) • v := by
    ext i
    rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.mulVec_diagonal,
      Pi.smul_apply, smul_eq_mul]
  rw [hmul, ← hQ₀, QuadraticMap.map_smul, smul_eq_mul] at h
  have h' : ((c : K) * c - 1) * Q v = 0 := by linear_combination h
  rw [pow_two]
  exact sub_eq_zero.1 ((mul_eq_zero.1 h').resolve_right hv)

theorem det_eq_one_of_mem_statedOmega {A : GL σ K} (hA : A ∈ StatedOmega Q₀) :
    (A : Matrix σ σ K).det = 1 := by
  have hle : StatedOmega Q₀ ≤ (Matrix.GeneralLinearGroup.det (n := σ) (R := K)).ker :=
    Subgroup.commutator_le.2 fun a _ b _ => by
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_commute]
      exact Commute.all _ _
  have h := hle hA
  rw [MonoidHom.mem_ker] at h
  rw [← Matrix.GeneralLinearGroup.val_det_apply, h, Units.val_one]

end Omega

section Spin

variable {σ : Type} [Fintype σ] [DecidableEq σ] {K : Type} [Field K]
  (Q : QuadraticForm K (σ → K))

theorem finite_spinGroup_of_ker [Finite K] {x : spinGroup Q}
    (hker : ((spinMatrix Q).ker : Set (spinGroup Q)) = {1, x}) : Finite (spinGroup Q) := by
  rw [MonoidHom.finite_iff_finite_ker_range (spinMatrix Q)]
  refine ⟨?_, inferInstance⟩
  have hfin : ((spinMatrix Q).ker : Set (spinGroup Q)).Finite :=
    hker ▸ (Set.finite_singleton x).insert 1
  exact hfin.to_subtype

theorem card_ker_spinMatrix_le_two {x : spinGroup Q}
    (hker : ((spinMatrix Q).ker : Set (spinGroup Q)) = {1, x}) :
    Nat.card (spinMatrix Q).ker ≤ 2 := by
  have h : Nat.card (spinMatrix Q).ker = ((spinMatrix Q).ker : Set (spinGroup Q)).ncard :=
    Nat.card_coe_set_eq _
  rw [h, hker]
  exact (Set.ncard_insert_le 1 {x}).trans (by rw [Set.ncard_singleton])

variable {Q} {Q₀ : (σ → K) → K}

theorem card_comap_statedScalars_le_four [Finite K] (hQ₀ : ⇑Q = Q₀) (hv : ∃ v, Q v ≠ 0)
    (hR : (spinMatrix Q).range = StatedOmega Q₀) {x : spinGroup Q}
    (hker : ((spinMatrix Q).ker : Set (spinGroup Q)) = {1, x}) :
    Nat.card ((StatedScalars σ K).comap (spinMatrix Q)) ≤ 4 := by
  have := finite_spinGroup_of_ker Q hker
  set Z := (StatedScalars σ K).comap (spinMatrix Q)
  let g : Z →* GL σ K := (spinMatrix Q).comp Z.subtype
  have h1 : Nat.card Z = Nat.card g.range * Nat.card g.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup g.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange g).toEquiv]
  have hkerg : Nat.card g.ker ≤ 2 := by
    refine (Nat.card_le_card_of_injective
      (fun z : g.ker => (⟨((z : Z) : spinGroup Q), z.2⟩ : (spinMatrix Q).ker)) ?_).trans
      (card_ker_spinMatrix_le_two Q hker)
    intro a b hab
    exact Subtype.ext (Subtype.ext (congrArg (fun y : (spinMatrix Q).ker => (y : spinGroup Q)) hab))
  have hrange : Nat.card g.range ≤ 2 := by
    refine card_le_two_of_forall_scalar (φ := g.range.subtype) Subtype.val_injective
      fun M => ?_
    obtain ⟨z, hz⟩ := M.2
    obtain ⟨c, hc⟩ : spinMatrix Q (z : spinGroup Q) ∈ StatedScalars σ K := z.2
    have hmem : Matrix.GeneralLinearGroup.scalar σ c ∈ StatedOmega Q₀ := by
      rw [hc, ← hR]
      exact ⟨_, rfl⟩
    refine ⟨c, sq_eq_one_of_scalar_mem_statedOmega hQ₀ hv hmem, ?_⟩
    change ((M : GL σ K) : Matrix σ σ K) = _
    rw [← hz]
    change ((spinMatrix Q (z : spinGroup Q) : GL σ K) : Matrix σ σ K) = _
    rw [← hc, Matrix.GeneralLinearGroup.coe_scalar]
  rw [h1]
  calc Nat.card g.range * Nat.card g.ker ≤ 2 * 2 := Nat.mul_le_mul hrange hkerg
    _ = 4 := by norm_num

theorem comap_statedScalars_le_ker_of_odd (hodd : Odd (Fintype.card σ)) (h2 : (2 : K) ≠ 0)
    (hQ₀ : ⇑Q = Q₀) (hv : ∃ v, Q v ≠ 0) (hR : (spinMatrix Q).range = StatedOmega Q₀) :
    (StatedScalars σ K).comap (spinMatrix Q) ≤ (spinMatrix Q).ker := by
  intro z hz
  obtain ⟨c, hc⟩ : spinMatrix Q z ∈ StatedScalars σ K := hz
  have hmem : Matrix.GeneralLinearGroup.scalar σ c ∈ StatedOmega Q₀ := by
    rw [hc, ← hR]
    exact ⟨_, rfl⟩
  have hsq := sq_eq_one_of_scalar_mem_statedOmega hQ₀ hv hmem
  have hdet := det_eq_one_of_mem_statedOmega hmem
  rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal,
    Finset.prod_const, Finset.card_univ] at hdet
  have hc1 : (c : K) = 1 := by
    rcases (mul_self_eq_one_iff (a := (c : K))).1 (by rw [← pow_two]; exact hsq) with h | h
    · exact h
    · rw [h, hodd.neg_one_pow] at hdet
      exact absurd (by linear_combination -hdet : (2 : K) = 0) h2
  rw [MonoidHom.mem_ker, ← hc]
  exact Units.ext (by rw [Matrix.GeneralLinearGroup.coe_scalar, hc1, map_one, Units.val_one])

end Spin


end CFSG.LieType.Steinberg
