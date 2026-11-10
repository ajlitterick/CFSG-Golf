module

public import CFSG.GroupTheory.ABGLocalTools.PStabilityDefs
import CFSG.GroupTheory.ABGLocalTools.Criteria
import CFSG.GroupTheory.CyclicSylowNormalOddComplement
import CFSG.GroupTheory.QuasiDihedralFusion.OddKernel
import CFSG.LocalAnalysis.SignalizerFunctor.InvariantSylowSupplements
import CFSG.LocalAnalysis.SignalizerFunctor.PrimeValueHull

public section

open Subgroup
open scoped Pointwise

namespace CFSG.ABGLocalTools

variable {H : Type*} [Group H] {p : ℕ}

section Coprime

variable [Finite H]

theorem exists_invariant_isSylowOf_ge_of_coprime {q r : ℕ} (hq : q.Prime) (hr : r.Prime)
    {A K P : Subgroup H} (hA : IsPGroup q A) (hAK : A ≤ normalizer (K : Set H))
    (hK : ¬ q ∣ Nat.card K) (hPK : P ≤ K) (hP : IsPGroup r P)
    (hAP : A ≤ normalizer (P : Set H)) :
    ∃ R : Subgroup H, IsSylowOf r R K ∧ P ≤ R ∧ A ≤ normalizer (R : Set H) := by
  let _action := CFSG.SignalizerFunctor.Helpers.conjugationAction A K hAK
  obtain ⟨Q, hPQ, hQ⟩ := CFSG.SignalizerFunctor.Helpers.invariant_sylow_containing q r hq hr hA
    ((Nat.Prime.coprime_iff_not_dvd hq).mpr hK) (P.subgroupOf K) hP.comap_subtype
    (CFSG.SignalizerFunctor.Helpers.normalized_subgroup_invariant_subgroup A K P hAK hAP)
  refine ⟨(Q : Subgroup K).map K.subtype, ⟨Q, rfl⟩, ?_, ?_⟩
  · rw [← Subgroup.map_subgroupOf_eq_of_le hPK]
    exact Subgroup.map_mono hPQ
  · apply CFSG.SignalizerFunctor.Helpers.invariant_subgroup_map_normalized A K hAK
    change ∀ a : A, ∀ x ∈ (Q : Subgroup K), a • x ∈ (Q : Subgroup K)
    intro a x hx
    have hmem := Subgroup.smul_mem_pointwise_smul x a (Q : Subgroup K) hx
    rwa [← Sylow.pointwise_smul_def, hQ a] at hmem

end Coprime

section Maximal

variable [Finite H] [Fact p.Prime]

omit [Finite H] in
theorem inf_eq_bot_of_isPGroup_two (hp : p ≠ 2) {Q D : Subgroup H} (hQ : IsPGroup p Q)
    (hD : IsPGroup 2 D) : Q ⊓ D = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact disjoint_iff.mp (IsPGroup.disjoint_of_ne p 2 hp Q D hQ hD)

omit [Finite H] in
theorem IsMaximalPSignalizer.eq_of_le (hp : p ≠ 2) {D R Q : Subgroup H} (hD : IsPGroup 2 D)
    (hR : IsMaximalPSignalizer D p R) (hRQ : R ≤ Q) (hQ : IsPGroup p Q)
    (hDQ : D ≤ normalizer (Q : Set H)) : Q = R :=
  hR.2 Q ⟨hQ, hDQ, inf_eq_bot_of_isPGroup_two hp hQ hD⟩ hRQ

theorem IsMaximalPSignalizer.isSylowOf_of_odd (hp : p ≠ 2) {D R W : Subgroup H}
    (hD : IsPGroup 2 D) (hR : IsMaximalPSignalizer D p R) (hRW : R ≤ W)
    (hW : Odd (Nat.card W)) (hDW : D ≤ normalizer (W : Set H)) : IsSylowOf p R W := by
  obtain ⟨Q, hQ, hRQ, hDQ⟩ := exists_invariant_isSylowOf_ge_of_coprime Nat.prime_two Fact.out hD
    hDW hW.not_two_dvd_nat hRW hR.1.1 hR.1.2.1
  rwa [hR.eq_of_le hp hD hRQ hQ.isPGroup hDQ] at hQ

theorem odd_card_sup_oddCore (hp : p ≠ 2) {R : Subgroup H} (hR : IsPGroup p R) :
    Odd (Nat.card (R ⊔ oddCore H : Subgroup H)) := by
  have hpp : p.Prime := Fact.out
  have h1 := Subgroup.relIndex_mul_card (oddCore H) (R ⊔ oddCore H)
  rw [inf_eq_left.mpr le_sup_right, relIndex_sup_right] at h1
  rw [← h1]
  refine Odd.mul ?_ (odd_card_oddCore (H := H))
  obtain ⟨k, hk⟩ := hR.exists_card_eq
  have hdvd : (oddCore H).relIndex R ∣ p ^ k := hk ▸ Subgroup.relIndex_dvd_card _ _
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hpp).mp hdvd
  rw [hj]
  exact (hpp.odd_of_ne_two hp).pow


end Maximal

section Covers

variable [Finite H] [Fact p.Prime]

theorem pCore_le_of_not_dvd_index {G : Type*} [Group G] [Finite G] {B : Subgroup G}
    (hB : ¬ p ∣ B.index) : pCore p G ≤ B := by
  have hdvd1 : B.relIndex (pCore p G ⊔ B) ∣ B.index := relIndex_dvd_index_of_le le_sup_right
  rw [relIndex_sup_eq_relIndex_of_normal] at hdvd1
  obtain ⟨k, hk⟩ := (pCore_isPGroup (p := p) (G := G)).exists_card_eq
  have hdvd2 : B.relIndex (pCore p G) ∣ p ^ k := hk ▸ relIndex_dvd_card _ _
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Fact.out).mp hdvd2
  have hj0 : j = 0 := by
    by_contra hj0
    apply hB
    rw [hj] at hdvd1
    exact (dvd_pow_self p hj0).trans hdvd1
  rw [hj0, pow_zero, relIndex_eq_one] at hj
  exact hj


omit [Fact p.Prime] in
theorem relIndex_sup_dvd_relIndex {A B K : Subgroup H} [K.Normal] (hAB : A ≤ B) :
    (A ⊔ K).relIndex (B ⊔ K) ∣ A.relIndex B := by
  have e1 := relIndex_mul_relIndex A B (B ⊔ K) hAB le_sup_left
  have e2 := relIndex_mul_relIndex A (A ⊔ K) (B ⊔ K) le_sup_left (sup_le_sup_right hAB K)
  have e3 : B.relIndex (B ⊔ K) = B.relIndex K := by
    rw [sup_comm]
    exact relIndex_sup_eq_relIndex_of_normal K B
  have e4 : A.relIndex (A ⊔ K) = A.relIndex K := by
    rw [sup_comm]
    exact relIndex_sup_eq_relIndex_of_normal K A
  have e5 := relIndex_mul_relIndex (A ⊓ K) (B ⊓ K) K (inf_le_inf_right K hAB) inf_le_right
  rw [inf_relIndex_right, inf_relIndex_right] at e5
  have hne : B.relIndex K ≠ 0 := by
    unfold Subgroup.relIndex
    exact Subgroup.index_ne_zero_of_finite
  have key : A.relIndex B * B.relIndex K =
      ((A ⊓ K).relIndex (B ⊓ K) * (A ⊔ K).relIndex (B ⊔ K)) * B.relIndex K := by
    calc A.relIndex B * B.relIndex K = A.relIndex B * B.relIndex (B ⊔ K) := by rw [e3]
      _ = A.relIndex (A ⊔ K) * (A ⊔ K).relIndex (B ⊔ K) := by rw [e1, e2]
      _ = (A ⊓ K).relIndex (B ⊓ K) * B.relIndex K * (A ⊔ K).relIndex (B ⊔ K) := by
          rw [e4, e5]
      _ = _ := by ring
  rw [Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hne) key]
  exact dvd_mul_left _ _

omit [Finite H] [Fact p.Prime] in
theorem mem_normalizer_of_conj_mem {g : H} {K : Subgroup H} (h1 : ∀ k ∈ K, g * k * g⁻¹ ∈ K)
    (h2 : ∀ k ∈ K, g⁻¹ * k * g ∈ K) : g ∈ normalizer (K : Set H) := by
  rw [mem_normalizer_iff]
  intro k
  refine ⟨h1 k, fun hk => ?_⟩
  have := h2 _ hk
  simpa [mul_assoc] using this

omit [Finite H] in
theorem odd_card_of_isPGroup (hp : p ≠ 2) {G : Type*} [Group G] [Finite G] {X : Subgroup G}
    (hX : IsPGroup p X) : Odd (Nat.card X) := by
  obtain ⟨k, hk⟩ := hX.exists_card_eq
  rw [hk]
  exact ((Fact.out : p.Prime).odd_of_ne_two hp).pow

omit [Finite H] in
theorem card_comap_mk' (N : Subgroup H) [N.Normal] (V : Subgroup (H ⧸ N)) :
    Nat.card (V.comap (QuotientGroup.mk' N)) = Nat.card N * Nat.card V := by
  have hNV : N ≤ V.comap (QuotientGroup.mk' N) := by
    intro n hn
    rw [mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff n).mpr hn]
    exact one_mem _
  have h1 := relIndex_mul_card N (V.comap (QuotientGroup.mk' N))
  rw [inf_eq_left.mpr hNV] at h1
  have h2 : N.relIndex (V.comap (QuotientGroup.mk' N)) = Nat.card V := by
    have h := relIndex_comap (H := (⊥ : Subgroup (H ⧸ N))) (QuotientGroup.mk' N)
      (V.comap (QuotientGroup.mk' N))
    rw [MonoidHom.comap_bot, QuotientGroup.ker_mk', map_comap_eq_self_of_surjective
      (QuotientGroup.mk'_surjective N), relIndex_bot_left] at h
    exact h
  rw [← h1, h2, mul_comm]


omit [Finite H] [Fact p.Prime] in
theorem mem_normalizer_map_subtype_of_characteristic {M : Subgroup H} {C : Subgroup M}
    [hC : C.Characteristic] {d : H} (hd : d ∈ normalizer (M : Set H)) :
    d ∈ normalizer ((C.map M.subtype : Subgroup H) : Set H) := by
  set α := normalizerMonoidHom M ⟨d, hd⟩ with hαdef
  have hα : ∀ m : M, ((α m : M) : H) = d * m * d⁻¹ := fun m =>
    normalizerMonoidHom_apply_apply_coe M ⟨d, hd⟩ m
  have hfix : C.comap α.toMonoidHom = C := hC.fixed α
  have hiff : ∀ m : M, α m ∈ C ↔ m ∈ C := fun m => by
    conv_rhs => rw [← hfix]
    rfl
  rw [mem_normalizer_iff]
  intro h
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact ⟨α m, (hiff m).mpr hm, hα m⟩
  · rintro ⟨m', hm', hm'eq⟩
    have hhM : h ∈ M := (mem_normalizer_iff.mp hd h).mpr (hm'eq ▸ m'.2)
    refine ⟨⟨h, hhM⟩, (hiff _).mp ?_, rfl⟩
    have : α ⟨h, hhM⟩ = m' := Subtype.ext (by rw [hα]; exact hm'eq.symm)
    rw [this]
    exact hm'


theorem comap_pCore_le_solvableRadical {K : Subgroup H} [K.Normal]
    (hK : K ≤ solvableRadical H) :
    (pCore p (H ⧸ K)).comap (QuotientGroup.mk' K) ≤ solvableRadical H := by
  set Y := (pCore p (H ⧸ K)).comap (QuotientGroup.mk' K) with hY
  have hYn : Y.Normal := (pCore_normal (p := p) (G := H ⧸ K)).comap _
  have hKY : K ≤ Y := by
    intro k hk
    rw [hY, mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff k).mpr hk]
    exact one_mem _
  have hKsolv : Group.IsSolvable K := by
    have := solvableRadical_isSolvable (H := H)
    exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hK)
      (Subgroup.inclusion_injective hK)
  have hNsolv : Group.IsSolvable (pCore p (H ⧸ K)) := by
    have := (pCore_isPGroup (p := p) (G := H ⧸ K)).isNilpotent
    infer_instance
  let g : Y →* pCore p (H ⧸ K) :=
    ((QuotientGroup.mk' K).comp Y.subtype).codRestrict _ fun y => y.2
  have hker : g.ker ≤ (Subgroup.inclusion hKY).range := by
    intro y hy
    have h1 : ((g y : pCore p (H ⧸ K)) : H ⧸ K) = 1 := by rw [MonoidHom.mem_ker.mp hy]; rfl
    have h2 : ((g y : pCore p (H ⧸ K)) : H ⧸ K) = QuotientGroup.mk' K (y : H) := rfl
    rw [h2, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact ⟨⟨y, h1⟩, rfl⟩
  have hYsolv : Group.IsSolvable Y := Group.isSolvable_of_ker_le_range _ g hker
  exact le_sSup ⟨hYn, hYsolv⟩


end Covers


section Ambient

omit [Group H] in
theorem subgroupOf_mem_pSignalizers_iff {G : Type*} [Group G] {K D X : Subgroup G}
    (hDK : D ≤ K) (hXK : X ≤ K) :
    X.subgroupOf K ∈ pSignalizers (D.subgroupOf K) p ↔
      IsPGroup p X ∧ D ≤ normalizer (X : Set G) ∧ X ⊓ D = ⊥ := by
  have e : X.subgroupOf K ≃* X := subgroupOfEquivOfLe hXK
  refine and_congr ⟨fun h => h.of_equiv e, fun h => h.of_equiv e.symm⟩ (and_congr ?_ ?_)
  · constructor
    · intro h d hd
      have hn := h (show (⟨d, hDK hd⟩ : K) ∈ D.subgroupOf K from hd)
      rw [mem_normalizer_iff] at hn ⊢
      intro x
      constructor
      · intro hx
        exact (hn ⟨x, hXK hx⟩).mp hx
      · intro hx
        have hxK : x ∈ K := by
          have hdK := hDK hd
          have : d⁻¹ * (d * x * d⁻¹) * d ∈ K := mul_mem (mul_mem (inv_mem hdK) (hXK hx)) hdK
          simpa [mul_assoc] using this
        exact (hn ⟨x, hxK⟩).mpr hx
    · intro h d hd
      have hn := h (mem_subgroupOf.mp hd)
      rw [mem_normalizer_iff] at hn ⊢
      intro x
      exact hn x
  · have h1 : X.subgroupOf K ⊓ D.subgroupOf K = (X ⊓ D).subgroupOf K := (comap_inf _ _ _).symm
    rw [h1, subgroupOf_eq_bot, disjoint_iff, inf_eq_left.mpr (inf_le_left.trans hXK)]

omit [Group H] in
theorem isMaximalPSignalizer_subgroupOf_iff {G : Type*} [Group G] {K D R : Subgroup G}
    (hDK : D ≤ K) (hRK : R ≤ K) :
    IsMaximalPSignalizer (D.subgroupOf K) p (R.subgroupOf K) ↔
      (IsPGroup p R ∧ D ≤ normalizer (R : Set G) ∧ R ⊓ D = ⊥) ∧
        ∀ R' : Subgroup G, R' ≤ K → IsPGroup p R' → D ≤ normalizer (R' : Set G) →
          R' ⊓ D = ⊥ → R ≤ R' → R' = R := by
  rw [IsMaximalPSignalizer, subgroupOf_mem_pSignalizers_iff hDK hRK]
  refine and_congr_right fun _ =>
    ⟨fun h R' hR'K hp' hn' hb' hRR' => ?_, fun h R'' hmem'' hRR'' => ?_⟩
  · have := h (R'.subgroupOf K) ((subgroupOf_mem_pSignalizers_iff hDK hR'K).mpr ⟨hp', hn', hb'⟩)
      (subgroupOf_mono K hRR')
    rw [subgroupOf_inj, inf_eq_left.mpr hR'K, inf_eq_left.mpr hRK] at this
    exact this
  · set R' := R''.map K.subtype with hR'def
    have hR'K : R' ≤ K := map_subtype_le _
    have hsub : R'.subgroupOf K = R'' := by
      rw [hR'def, subgroupOf, comap_map_eq_self_of_injective K.subtype_injective]
    rw [← hsub] at hmem'' hRR''
    obtain ⟨hp', hn', hb'⟩ := (subgroupOf_mem_pSignalizers_iff hDK hR'K).mp hmem''
    have hRR' : R ≤ R' := by
      have := map_mono (f := K.subtype) hRR''
      rwa [subgroupOf_map_subtype, subgroupOf_map_subtype, inf_eq_left.mpr hRK,
        inf_eq_left.mpr hR'K] at this
    rw [← hsub, h R' hR'K hp' hn' hb' hRR']

end Ambient

end CFSG.ABGLocalTools
