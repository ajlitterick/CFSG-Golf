module

public import CFSG.Milestones.ASVolI.A2
public import CFSG.RankThree.PartOne.CTP.SpAut
public import CFSG.RankThree.PartTwo.Sec8.Item8KFactsProofG2
public import CFSG.RankThree.PartTwo.KFacts.AutPSUInner
public import CFSG.SignalizerFunctorTheorem.McBride.Models.PSL2Even.Aut

public section

namespace CFSG.ASVolI

open CFSG.Open

section Induced

variable {G : Type} [Group G] (L : Subgroup G) [L.Normal]


end Induced


section Induced2

variable {G : Type} [Group G] (L : Subgroup G) [L.Normal]


end Induced2


theorem burnsideA26_congr_congr_symm {S M : Type*} [Group S] [Group M] (e : S ≃* M)
    (φ : MulAut M) : MulAut.congr e (MulAut.congr e.symm φ) = φ := by
  ext x
  simp [MulAut.congr_apply]

theorem burnsideA26_congr_symm_congr {S M : Type*} [Group S] [Group M] (e : S ≃* M)
    (φ : MulAut S) : MulAut.congr e.symm (MulAut.congr e φ) = φ := by
  ext x
  simp [MulAut.congr_apply]

theorem burnsideA26_charP_two {K : Type} [Field K] [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) :
    CharP K 2 := by
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact charP_of_card_eq_prime_pow (p := 2) (f := n) (by rw [← Nat.card_eq_fintype_card, hK])


theorem burnsideA26_congr_trans_apply {S Q A : Type*} [Group S] [Group Q] [Group A]
    (e : S ≃* Q) (κ : Q ≃* A) (F : MulAut A) (q : Q) :
    MulAut.congr e (MulAut.congr (e.trans κ).symm F) q = κ.symm (F (κ q)) := by
  simp [MulAut.congr_apply]

section Sp4Fam

open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.RankThree.PartTwo.KFacts


end Sp4Fam

section G2Fam

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley


end G2Fam

section SzFam

open CFSG.Blueprint


end SzFam


section ReeF4Fam

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.LieType.Ree.ReeTag


end ReeF4Fam

section RankFam


end RankFam

section CenterFam

open CFSG.SectionRank


end CenterFam

section G2E9Fam

open CFSG.Blueprint.Chevalley
open CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof


end G2E9Fam

section ExistsZFam


end ExistsZFam

section L2Fam

open CFSG.Assembly.LowTwoRank CFSG.GorensteinWalter
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo


end L2Fam

section D4AbsFam

open CFSG.RankThree.PartTwo.KFacts


end D4AbsFam

section D4Fam

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.PartTwo.KFacts


end D4Fam

section LnFam

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

@[expose] noncomputable def burnsideA26_statedToProjSL (n : ℕ) (K : Type) [Field K] :
    StatedProj (StatedSL n K) ≃* projectiveSL n K :=
  (projectiveSpecialLinearGroupEquivStatedProj n K).symm.trans
    (LinearCover.projectiveSpecialLinearEquivProjectiveSL n K)

theorem burnsideA26_statedToProjSL_mk (n : ℕ) (K : Type) [Field K]
    (u : Matrix.SpecialLinearGroup (Fin n) K) :
    burnsideA26_statedToProjSL n K
        (QuotientGroup.mk (specialLinearGroupEquivStatedSL n K u) : StatedProj (StatedSL n K)) =
      LinearFlag.proj n K u := by
  have h1 : (projectiveSpecialLinearGroupEquivStatedProj n K).symm
      (QuotientGroup.mk (specialLinearGroupEquivStatedSL n K u) : StatedProj (StatedSL n K)) =
      QuotientGroup.mk' (Subgroup.center _) u := by
    apply (projectiveSpecialLinearGroupEquivStatedProj n K).injective
    rw [MulEquiv.apply_symm_apply]
    rfl
  show LinearCover.projectiveSpecialLinearEquivProjectiveSL n K
    ((projectiveSpecialLinearGroupEquivStatedProj n K).symm
      (QuotientGroup.mk (specialLinearGroupEquivStatedSL n K u) : StatedProj (StatedSL n K))) = _
  rw [h1]
  exact QuotientGroup.quotientMulEquivOfEq_mk _ u

theorem burnsideA26_statedToProjSL_symm_proj (n : ℕ) (K : Type) [Field K]
    (u : Matrix.SpecialLinearGroup (Fin n) K) :
    (burnsideA26_statedToProjSL n K).symm (LinearFlag.proj n K u) =
      (QuotientGroup.mk (specialLinearGroupEquivStatedSL n K u) : StatedProj (StatedSL n K)) :=
  (burnsideA26_statedToProjSL n K).symm_apply_eq.2 (burnsideA26_statedToProjSL_mk n K u).symm

theorem burnsideA26_isProjConjAut {n : ℕ} {S : Type} [Group S] {K : Type} [Field K]
    (e : S ≃* StatedProj (StatedSL n K)) (A : GL (Fin n) K) :
    ChA.IsProjConjAut (StatedSL n K) A
      (MulAut.congr e (MulAut.congr (e.trans (burnsideA26_statedToProjSL n K)).symm
        (LinearFlag.conjAut n K A))) := by
  intro g
  obtain ⟨u, hu⟩ := (specialLinearGroupEquivStatedSL n K).surjective g
  refine ⟨specialLinearGroupEquivStatedSL n K
    (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation n K A u), ?_, ?_⟩
  · rw [← hu]
    apply Units.ext
    rw [Units.val_mul, Units.val_mul]
    exact coe_slConjugation A u
  · rw [burnsideA26_congr_trans_apply, ← hu, burnsideA26_statedToProjSL_mk, conjAut_proj,
      burnsideA26_statedToProjSL_symm_proj]

theorem burnsideA26_isProjFieldAut {n : ℕ} {S : Type} [Group S] {K : Type} [Field K]
    (e : S ≃* StatedProj (StatedSL n K)) (σ : K ≃+* K) :
    ChA.IsProjFieldAut (StatedSL n K) σ
      (MulAut.congr e (MulAut.congr (e.trans (burnsideA26_statedToProjSL n K)).symm
        (fieldAut n K σ))) := by
  intro g
  obtain ⟨u, hu⟩ := (specialLinearGroupEquivStatedSL n K).surjective g
  refine ⟨specialLinearGroupEquivStatedSL n K (Matrix.SpecialLinearGroup.map σ.toRingHom u),
    ?_, ?_⟩
  · rw [← hu]
    apply Units.ext
    rfl
  · rw [burnsideA26_congr_trans_apply, ← hu, burnsideA26_statedToProjSL_mk, fieldAut_proj,
      burnsideA26_statedToProjSL_symm_proj]


end LnFam

section U3Fam

open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartTwo.KFacts
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)

theorem burnsideA26_psuPow {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)
    (A : unitaryIsom3 h) (σ : K ≃+* K) (k : ℕ) :
    ∃ N : unitaryIsom3 h, (psuConj h A * psuField h σ) ^ k =
      psuConj h N * psuField h (σ ^ k) := by
  induction k with
  | zero => exact ⟨1, by simp⟩
  | succ k ih =>
    obtain ⟨N, hN⟩ := ih
    refine ⟨N * ⟨glAut (σ ^ k) A, glAut_mem_unitaryIsom3 (σ ^ k) A.2⟩, ?_⟩
    rw [pow_succ, hN, pow_succ, map_mul, map_mul, ← psuField_mul_psuConj_mul_inv]
    group

theorem burnsideA26_u3_odd {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)
    (hq : 2 < p ^ f) {S : Type} [Group S] (e : S ≃* unitaryPSU h 3) (θ : MulAut S)
    (hθ : Odd (orderOf θ)) :
    ∃ (A : unitaryIsom3 h) (σ : K ≃+* K), MulAut.congr e θ = psuConj h A * psuField h σ ∧
      Odd (orderOf σ) := by
  obtain ⟨A, σ, hAσ⟩ := exists_psuConj_mul_psuField hq (MulAut.congr e θ)
  refine ⟨A, σ, hAσ, ?_⟩
  have h1 : (psuConj h A * psuField h σ) ^ orderOf θ = 1 := by
    rw [← hAσ, ← map_pow, pow_orderOf_eq_one, map_one]
  obtain ⟨N, hN⟩ := burnsideA26_psuPow h A σ (orderOf θ)
  rw [hN] at h1
  have h2 := (eq_one_of_psuConj_mul_psuField_eq_one N (σ ^ orderOf θ) h1).1
  exact hθ.of_dvd_nat (orderOf_dvd_of_pow_eq_one h2)

theorem burnsideA26_isProjConjAut_u3 {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)
    {S : Type} [Group S] (e : S ≃* StatedProj (StatedSU 3 (p ^ f) K)) (A : unitaryIsom3 h) :
    ChA.IsProjConjAut (StatedSU 3 (p ^ f) K) (A : GL (Fin 3) K)
      (MulAut.congr e (MulAut.congr (e.trans (unitaryPSUEquiv h (by norm_num : 1 ≤ 3)).symm).symm
        (psuConj h A))) := by
  intro g
  refine ⟨suConj h A g, rfl, ?_⟩
  rw [burnsideA26_congr_trans_apply]
  have h1 : (unitaryPSUEquiv h (by norm_num : 1 ≤ 3)).symm.symm
      (psuConj h A ((unitaryPSUEquiv h (by norm_num : 1 ≤ 3)).symm (QuotientGroup.mk g))) =
      QuotientGroup.mk (suConj h A g) := by
    have e1 : (unitaryPSUEquiv h (by norm_num : 1 ≤ 3)).symm
        (QuotientGroup.mk g : StatedProj (StatedSU 3 (p ^ f) K)) = unitaryProj h 3 g := by
      apply (unitaryPSUEquiv h (by norm_num : 1 ≤ 3)).injective
      rw [MulEquiv.apply_symm_apply, unitaryPSUEquiv_unitaryProj]
    rw [e1]
    show unitaryPSUEquiv h (by norm_num : 1 ≤ 3) (unitaryProj h 3 (suConj h A g)) = _
    exact unitaryPSUEquiv_unitaryProj h _ _
  exact h1


theorem burnsideA26_u33 {S : Type} [Group S] {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (3 ^ 1) ^ 2) (e : S ≃* StatedProj (StatedSU 3 (3 ^ 1) K)) (θ : MulAut S)
    (hθ : Odd (orderOf θ)) : (MulAut.conj : S →* MulAut S).range.carrier θ := by
  have h : UnitaryFieldData 3 1 K := ⟨Nat.prime_three, le_rfl, by rw [hK]; norm_num⟩
  have hq : 2 < 3 ^ 1 := by norm_num
  obtain ⟨A, σ, hAσ, hodd⟩ := burnsideA26_u3_odd h hq
    (e.trans (unitaryPSUEquiv h (by norm_num : 1 ≤ 3)).symm) θ hθ
  have hK9 : Nat.card K = 3 ^ 2 := by rw [hK]; norm_num
  have hcard := (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic Nat.prime_three K
    hK9).1
  have hσ2 : σ ^ 2 = 1 := by
    have := pow_card_eq_one' (G := RingAut K) (x := σ)
    rwa [hcard] at this
  have hσ : σ = 1 := by
    obtain ⟨m, hm⟩ := hodd
    have h1 : σ ^ (2 * m) = 1 := by rw [pow_mul, hσ2, one_pow]
    have h2 : σ ^ (2 * m + 1) = σ := by rw [pow_succ, h1, one_mul]
    rw [← h2, ← hm]
    exact pow_orderOf_eq_one σ
  have hnorm : h.norm (Matrix.GeneralLinearGroup.det (A : GL (Fin 3) K) : K) = 1 := by
    rw [Matrix.GeneralLinearGroup.val_det_apply]
    exact norm_det_of_mem_unitaryIsom3 A.2
  have hnx : ∀ x : K, h.norm x = x ^ 4 := fun x => by
    rw [UnitaryFieldData.norm, UnitaryFieldData.bar_apply]
    ring
  set d : Kˣ := Matrix.GeneralLinearGroup.det (A : GL (Fin 3) K)
  have hd4 : d ^ 4 = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, ← hnx, hnorm, Units.val_one]
  have hinner : psuConj h A ∈ (MulAut.conj : unitaryPSU h 3 →* MulAut (unitaryPSU h 3)).range := by
    refine psuConj_mem_range_conj_of_det_eq_pow (u := d ^ 3) ?_ ?_
    · rw [hnx, ← Units.val_pow_eq_pow_val, ← pow_mul, show 3 * 4 = 4 * 3 from rfl, pow_mul, hd4,
        one_pow, Units.val_one]
    · calc d = d * (d ^ 4) ^ 2 := by rw [hd4]; simp
        _ = (d ^ 3) ^ 3 := by group
  have hin : CFSG.RankThree.PartTwo.KFacts.IsInnerAut
      (MulAut.congr (e.trans (unitaryPSUEquiv h (by norm_num : 1 ≤ 3)).symm) θ) := by
    rw [hAσ, hσ, map_one, mul_one]
    exact hinner
  exact (CFSG.RankThree.PartTwo.KFacts.isInnerAut_congr
    (e.trans (unitaryPSUEquiv h (by norm_num : 1 ≤ 3)).symm) θ).1 hin

end U3Fam

section SmallFam

open CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.LocalAnalysis.ComponentInitial

theorem burnsideA26_psl2_odd_inner {K : Type} [Field K] [Finite K] {p k : ℕ} (hp : p.Prime)
    (hK : Nat.card K = p ^ k) (hk : k = 1 ∨ k = 2) {S : Type} [Group S] (e : S ≃* PSL2 K)
    (θ : MulAut S) (hθ : Odd (orderOf θ)) :
    (MulAut.conj : S →* MulAut S).range.carrier θ := by
  set φ : MulAut (PSL2 K) := MulAut.congr e θ with hφ
  have hφm : φ ^ orderOf θ = 1 := by rw [hφ, ← map_pow, pow_orderOf_eq_one, map_one]
  set γ := (semilinearEquivAut K).symm φ with hγ
  have hγm : γ ^ orderOf θ = 1 := by rw [hγ, ← map_pow, hφm, map_one]
  have hψ : (SemidirectProduct.rightHom γ) ^ orderOf θ = 1 := by rw [← map_pow, hγm, map_one]
  have hcard : Nat.card (RingAut K) = k :=
    (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic hp K hK).1
  have hcop : Nat.Coprime (orderOf θ) k := by
    rcases hk with rfl | rfl
    · exact Nat.coprime_one_right _
    · exact Nat.coprime_two_right.2 hθ
  have hord : orderOf (SemidirectProduct.rightHom γ) = 1 := by
    have h1 : orderOf (SemidirectProduct.rightHom γ) ∣ orderOf θ := orderOf_dvd_of_pow_eq_one hψ
    have h2 : orderOf (SemidirectProduct.rightHom γ) ∣ k := hcard ▸ orderOf_dvd_natCard _
    exact Nat.eq_one_of_dvd_coprimes hcop h1 h2
  have hψ1 : SemidirectProduct.rightHom γ = 1 := orderOf_eq_one_iff.mp hord
  obtain ⟨g, hg⟩ := CFSG.RankThree.PartTwo.KFacts.mem_range_pglAction_of_rightHom_eq_one hψ1
  have hg' : g ^ orderOf θ = 1 := by
    apply CFSG.RankThree.PartTwo.KFacts.pglAction_injective
    rw [map_pow, hg, hφm, map_one]
  obtain ⟨x, hx⟩ := CFSG.RankThree.PartTwo.KFacts.exists_toPGL_eq_of_pow_odd hθ hg'
  have hin : CFSG.RankThree.PartTwo.KFacts.IsInnerAut φ := by
    refine ⟨x, ?_⟩
    rw [← hg, ← hx]
    exact pglAction_toPGL K x ▸ rfl
  exact (CFSG.RankThree.PartTwo.KFacts.isInnerAut_congr e θ).1 hin

theorem burnsideA26_a6 {S : Type} [Group S] (e : S ≃* alternatingGroup (Fin 6)) (θ : MulAut S)
    (hθ : Odd (orderOf θ)) : (MulAut.conj : S →* MulAut S).range.carrier θ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK9 : Nat.card (GaloisField 3 2) = 3 ^ 2 := GaloisField.card 3 2 (by norm_num)
  haveI : Fintype (GaloisField 3 2) := Fintype.ofFinite _
  obtain ⟨e0⟩ := unique_field_nine_projective_linear_alternating_six_isomorphism
    (GaloisField 3 2) (by rw [← Nat.card_eq_fintype_card, hK9]; norm_num)
  exact burnsideA26_psl2_odd_inner Nat.prime_three hK9 (Or.inr rfl) (e.trans e0.symm) θ hθ


end SmallFam

section MainA26


end MainA26

end CFSG.ASVolI
