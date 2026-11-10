module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.NormalFourGeometry
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionGeometryZStar
public import CFSG.LocalAnalysis.SignalizerFunctor.Maximality
public import CFSG.LocalAnalysis.ComponentClassification.OddCore
public import CFSG.Adapters.Involutions

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore

open CFSG.Open CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki
open CFSG.SignalizerFunctor.Helpers CFSG.LargeEvenClassification.Helpers
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem involution_zpowers_elements {z a : G} (hz : orderOf z = 2)
    (ha : a ∈ Subgroup.zpowers z) : a = 1 ∨ a = z := by
  have hzneq : z ≠ 1 := by
    intro heq
    simp [heq] at hz
  have hcard : Nat.card (Subgroup.zpowers z) = 2 :=
    (Nat.card_zpowers z).trans hz
  obtain ⟨other, _, hunique⟩ :=
    (Nat.card_eq_two_iff' (1 : Subgroup.zpowers z)).mp hcard
  have hzinternal : (⟨z, Subgroup.mem_zpowers z⟩ : Subgroup.zpowers z) ≠ 1 :=
    fun heq => hzneq (congrArg Subtype.val heq)
  by_cases hone : (⟨a, ha⟩ : Subgroup.zpowers z) = 1
  · exact Or.inl (congrArg Subtype.val hone)
  · exact Or.inr (congrArg Subtype.val
      ((hunique _ hone).trans (hunique _ hzinternal).symm))

theorem commuting_distinct_involutions_four_group {z w : G}
    (hz : orderOf z = 2) (hw : orderOf w = 2)
    (hzw : Commute z w) (hne : w ≠ z) :
    IsElemAbelian 2 (Subgroup.zpowers z ⊔ Subgroup.zpowers w) ∧
      Nat.card (Subgroup.zpowers z ⊔ Subgroup.zpowers w : Subgroup G) = 4 ∧
      ∀ a ∈ (Subgroup.zpowers z ⊔ Subgroup.zpowers w : Subgroup G),
        a = 1 ∨ a = z ∨ a = w ∨ a = z * w := by
  let Z := Subgroup.zpowers z
  let W := Subgroup.zpowers w
  have hwneq : w ≠ 1 := by
    intro heq
    simp [heq] at hw
  have hwZ : w ∉ Z := by
    intro hwmem
    exact (involution_zpowers_elements hz hwmem).elim hwneq hne
  have hcommute : Z ≤ Subgroup.centralizer (W : Set G) := by
    intro a ha
    apply Subgroup.mem_centralizer_iff.mpr
    intro b hb
    rcases involution_zpowers_elements hz ha with rfl | rfl
    · simp
    · rcases involution_zpowers_elements hw hb with rfl | rfl
      · simp
      · exact hzw.symm.eq
  obtain ⟨A, hZA, hWA, hA, hcard, hAjoin⟩ :=
    commuting_disjoint_elementary_product (prime := 2)
      (firstRank := 1) (secondRank := 1) Z W
      (involution_zpowers_elementary z hz) (involution_zpowers_elementary w hw)
      ((Nat.card_zpowers z).trans hz) ((Nat.card_zpowers w).trans hw)
      hcommute (involution_zpowers_disjoint Z w hw hwZ)
  have hAeq : A = Z ⊔ W := le_antisymm hAjoin (sup_le hZA hWA)
  rw [hAeq] at hA hcard
  refine ⟨hA, by simpa using hcard, ?_⟩
  have hcomm : ∀ a : Z, ∀ b : W, Commute (Z.subtype a) (W.subtype b) := by
    intro a b
    exact (Subgroup.mem_centralizer_iff.mp (hcommute a.property)
      b b.property).symm
  let f := Z.subtype.noncommCoprod W.subtype hcomm
  have hrange : f.range = Z ⊔ W := by
    simpa only [Subgroup.subtype_range] using
      MonoidHom.noncommCoprod_range Z.subtype W.subtype hcomm
  intro a ha
  rw [← hrange] at ha
  obtain ⟨pair, rfl⟩ := ha
  change (pair.1 : G) * (pair.2 : G) = 1 ∨
    (pair.1 : G) * (pair.2 : G) = z ∨
    (pair.1 : G) * (pair.2 : G) = w ∨
    (pair.1 : G) * (pair.2 : G) = z * w
  rcases involution_zpowers_elements hz pair.1.property with hfirst | hfirst
  · rcases involution_zpowers_elements hw pair.2.property with hsecond | hsecond
    · exact Or.inl (by rw [hfirst, hsecond, one_mul])
    · exact Or.inr (Or.inr (Or.inl (by rw [hfirst, hsecond, one_mul])))
  · rcases involution_zpowers_elements hw pair.2.property with hsecond | hsecond
    · exact Or.inr (Or.inl (by rw [hfirst, hsecond, mul_one]))
    · exact Or.inr (Or.inr (Or.inr (by rw [hfirst, hsecond])))

omit [Finite G] in
theorem local_point_class_centralizer_le {H : Subgroup G} {z w : G}
    (h : InvolutionPointLocalEmbedding H z)
    (hw : w ∈ involutionPointClass z) (hwH : w ∈ H) :
    Subgroup.centralizer ({w} : Set G) ≤ H := by
  obtain ⟨a, rfl⟩ := hw
  have haH := (pointClass_conjugate_mem_iff h a).mp hwH
  intro g hg
  have hcomm := Subgroup.mem_centralizer_singleton_iff.mp hg
  have hfix : g⁻¹ * rightConjugateElem z a * g = rightConjugateElem z a := by
    rw [mul_assoc, ← hcomm, inv_mul_cancel_left]
  have hfixedmem : g⁻¹ * rightConjugateElem z a * g ∈ H := by
    rw [hfix]
    exact hwH
  have hag : rightConjugateElem z (a * g) ∈ H := by
    simpa only [rightConjugateElem, mul_inv_rev, mul_assoc] using hfixedmem
  have hagH := (pointClass_conjugate_mem_iff h (a * g)).mp hag
  simpa only [inv_mul_cancel_left] using H.mul_mem (H.inv_mem haH) hagH

theorem local_point_commuting_product_centralizer_le {H : Subgroup G} {z w : G}
    (h : InvolutionPointLocalEmbedding H z)
    (hw : w ∈ involutionPointClass z) (hzw : Commute z w) (hne : w ≠ z) :
    Subgroup.centralizer ({z * w} : Set G) ≤ H := by
  have hzsq : z * z = 1 := by
    simpa only [pow_two] using (orderOf_eq_prime_iff.mp h.distinguished_order).1
  have hworder := order_two_of_mem_pointClass h.distinguished_order hw
  have hwsq : w * w = 1 := by
    simpa only [pow_two] using (orderOf_eq_prime_iff.mp hworder).1
  have hproductneq : z * w ≠ 1 := by
    intro heq
    apply hne
    have heq' := congrArg (fun a : G => z * a) heq
    simpa only [← mul_assoc, hzsq, one_mul, mul_one] using heq'
  have hproductorder : orderOf (z * w) = 2 := by
    apply orderOf_eq_prime_iff.mpr
    refine ⟨?_, hproductneq⟩
    rw [hzw.mul_pow, pow_two, pow_two, hzsq, hwsq, one_mul]
  by_contra hescape
  have hnot := involution_point_product_not_mem h hproductorder
    ((Commute.refl z).mul_left hzw.symm) hescape
  have heq : (z * w) * z = w := by
    rw [mul_assoc, ← hzw.eq, ← mul_assoc, hzsq, one_mul]
  exact hnot (heq.symm ▸ hw)

theorem local_point_odd_subgroup_le_of_commuting_class
    {H : Subgroup G} {z w : G} (h : InvolutionPointLocalEmbedding H z)
    (hw : w ∈ involutionPointClass z) (hzw : Commute z w) (hne : w ≠ z)
    (X : Subgroup G) (hXodd : Odd (Nat.card X))
    (hnormalizes : Subgroup.zpowers z ⊔ Subgroup.zpowers w ≤
      Subgroup.normalizer (X : Set G)) : X ≤ H := by
  let A := Subgroup.zpowers z ⊔ Subgroup.zpowers w
  obtain ⟨hA, hAcard, hcases⟩ := commuting_distinct_involutions_four_group
    h.distinguished_order (order_two_of_mem_pointClass h.distinguished_order hw)
    hzw hne
  have hwH : w ∈ H := point_centralizer_le h
    (Subgroup.mem_centralizer_singleton_iff.mpr hzw.symm)
  have hwcentralizer := local_point_class_centralizer_le h hw hwH
  have hproductcentralizer := local_point_commuting_product_centralizer_le h hw hzw hne
  rw [← elementary_abelian_centralizer_generation 2 1 Nat.prime_two A X hA
    (by simpa using hAcard.ge) hnormalizes (Nat.coprime_two_left.mpr hXodd)]
  apply iSup_le
  intro U
  apply iSup_le
  intro hU
  have hUcard : Nat.card U = 2 := by simpa using hU.2
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := U) 2
    (by simp only [hUcard, dvd_refl])
  have haG : orderOf (a : G) = 2 := (Subgroup.orderOf_coe a).trans ha
  have haneq : (a : G) ≠ 1 := by
    intro heq
    simp [heq] at haG
  have haA : (a : G) ∈ A := hU.1 a.property
  have hcentralizer : Subgroup.centralizer (U : Set G) ≤
      Subgroup.centralizer ({(a : G)} : Set G) := by
    apply Subgroup.centralizer_le
    exact Set.singleton_subset_iff.mpr a.property
  apply (inf_le_right.trans hcentralizer).trans
  rcases hcases (a : G) haA with hone | hz | hw | hproduct
  · exact False.elim (haneq hone)
  · rw [hz]
    exact point_centralizer_le h
  · rw [hw]
    exact hwcentralizer
  · rw [hproduct]
    exact hproductcentralizer

theorem local_point_isolated_of_odd_normal_cover {H : Subgroup G} {z : G}
    (h : InvolutionPointLocalEmbedding H z) (X : Subgroup G) [X.Normal]
    (hXodd : Odd (Nat.card X)) (hcover : H ⊔ X = ⊤)
    {w : G} (hw : w ∈ involutionPointClass z) (hcomm : Commute w z) : w = z := by
  by_contra hne
  have hXH := local_point_odd_subgroup_le_of_commuting_class h hw hcomm.symm hne
    X hXodd (by rw [Subgroup.normalizer_eq_top]; exact le_top)
  have htop : (⊤ : Subgroup G) ≤ H := by
    rw [← hcover]
    exact sup_le le_rfl hXH
  exact h.proper (top_le_iff.mp htop)

theorem local_point_isolated_of_odd_core_cover {H : Subgroup G} {z : G}
    (h : InvolutionPointLocalEmbedding H z) (hcover : H ⊔ oddCore G = ⊤)
    {w : G} (hw : w ∈ involutionPointClass z) (hcomm : Commute w z) : w = z := by
  exact local_point_isolated_of_odd_normal_cover h (oddCore G)
    (CFSG.ComponentClassification.OddCore.odd_card G) hcover hw hcomm


end CFSG.ProperTwoGeneratedCore
