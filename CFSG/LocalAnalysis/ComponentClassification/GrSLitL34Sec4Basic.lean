module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4Inputs
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitConn
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitLemma228
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallL34Out
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aConjFix
public import CFSG.LocalAnalysis.ComponentClassification.GSLitBridge
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrTwoLocalOrbits

public section

namespace CFSG.ComponentClassification.GrSLit.GrS4

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
open scoped Pointwise

variable {G : Type} [Group G]

theorem le_pRank_of_isElemTwo [Finite G] {H E : Subgroup G} (hEH : E ≤ H) (hE : IsElemTwo E)
    {k : ℕ} (hk : Nat.card E = 2 ^ k) : k ≤ pRank 2 ↥H := by
  have hEA : IsElementaryAbelian 2 ↥(E.subgroupOf H) :=
    { is_comm := ⟨fun u v => Subtype.ext (Subtype.ext
        (hE.1 _ (mem_subgroupOf.mp u.2) _ (mem_subgroupOf.mp v.2)))⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun u =>
        Subtype.ext (Subtype.ext (by
          show ((u : H) : G) ^ 2 = 1
          rw [pow_two]
          exact hE.2 _ (mem_subgroupOf.mp u.2))) }
  have hcard : Nat.card ↥(E.subgroupOf H) = 2 ^ k := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hEH).toEquiv, hk]
  refine le_csSup ⟨Nat.card H, ?_⟩ ⟨E.subgroupOf H, hEA, hcard⟩
  rintro r ⟨B, -, hB⟩
  calc r ≤ 2 ^ r := (Nat.lt_two_pow_self).le
    _ = Nat.card B := hB.symm
    _ ≤ Nat.card H := card_le_card_group B

theorem isSylowTwoIn_inf [Finite G] {S J : Subgroup G}
    (hS : IsSylowTwoIn S (normalizer (J : Set G))) : IsSylowTwoIn (S ⊓ J) J := by
  obtain ⟨hSN, P, hP⟩ := hS
  obtain ⟨T, hT⟩ := RankProjectiveAction.exists_sylow_inf_of_le_normalizer hSN ⟨P, hP⟩
    le_normalizer le_rfl
  exact ⟨inf_le_right, T, hT⟩

theorem not_mem_coreActionKernel [Finite G] {a x : G} {J : Subgroup G}
    (h : GSUnbalancingTriple a x J) : x ∉ coreActionKernel J := by
  intro hx
  have hq := GSLit.isQuasisimple_of_gsUnbalancingTriple h
  have hle : J ≤ (pPrimeCore 2 J).map J.subtype := by
    calc J = closure {y | ∃ j ∈ J, y = j⁻¹ * x⁻¹ * j * x} := h.2.2.2.2.2.1.symm
      _ ≤ _ := by
        rw [closure_le]
        rintro y ⟨j, hj, rfl⟩
        exact (mem_coreActionKernel.mp hx).2 j hj
  have hall : ∀ u v : J ⧸ pPrimeCore 2 J, u = v := by
    intro u v
    induction u using QuotientGroup.induction_on with
    | H u =>
    induction v using QuotientGroup.induction_on with
    | H v =>
    rw [QuotientGroup.eq]
    obtain ⟨k, hk, hkj⟩ := hle (u⁻¹ * v).2
    rwa [show k = u⁻¹ * v from Subtype.ext hkj] at hk
  obtain ⟨-, -, a', b', hab⟩ := hq
  apply hab
  induction a' using QuotientGroup.induction_on with
  | H a' =>
  induction b' using QuotientGroup.induction_on with
  | H b' =>
  rw [hall a' b']

theorem sixtyFour_le_card [Finite G] {J P : Subgroup G}
    (hL34 : IsL34Type (J ⧸ Open.fusionZStar J)) (hP : IsSylowTwoIn P J) : 64 ≤ Nat.card P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hPJ, T, hT⟩ := hP
  obtain ⟨e⟩ := CatFactsSmall.nonempty_equiv_psl34_of_lieModel hL34
  have hcardQ : Nat.card (J ⧸ Open.fusionZStar J) = 20160 := by
    rw [Nat.card_congr e.toEquiv, PSL3Four.card_S]
  let T' := T.mapSurjective (QuotientGroup.mk'_surjective (Open.fusionZStar ↥J))
  have h1 : Nat.card T' = 64 := by
    rw [Sylow.card_eq_multiplicity, hcardQ,
      show (20160 : ℕ) = 2 ^ 6 * 315 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
      Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_two]
    simp [Nat.factorization_eq_zero_of_not_dvd (show ¬ 2 ∣ 315 by norm_num)]
  have h2 : Nat.card T' ≤ Nat.card T :=
    Nat.le_of_dvd Nat.card_pos (Subgroup.card_map_dvd (H := (T : Subgroup ↥J))
      (QuotientGroup.mk' (Open.fusionZStar ↥J)))
  have h3 : Nat.card T = Nat.card P := by
    rw [hT]
    exact Nat.card_congr (subgroupOfEquivOfLe hPJ).toEquiv
  omega

theorem not_le_coreActionKernel_self [Finite G] {C J : Subgroup G} (hJC : J ≤ C)
    (hJ : IsPComponent 2 (J.subgroupOf C)) : ¬ J ≤ coreActionKernel J := by
  intro h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, hq⟩ := (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 J C hJC).mp hJ
  obtain ⟨-, -, a, b, hab⟩ := hq
  apply hab
  induction a using QuotientGroup.induction_on with
  | H a =>
  induction b using QuotientGroup.induction_on with
  | H b =>
  induction a using QuotientGroup.induction_on with
  | H u =>
  induction b using QuotientGroup.induction_on with
  | H v =>
  have hc : (QuotientGroup.mk u : J ⧸ pPrimeCore 2 J) * QuotientGroup.mk v =
      QuotientGroup.mk v * QuotientGroup.mk u := by
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    have h1 := (mem_coreActionKernel.mp (h u.2)).2 v v.2
    obtain ⟨w, hw, hwe⟩ := h1
    have : w = (u * v)⁻¹ * (v * u) := by
      apply Subtype.ext
      rw [show (w : G) = _ from hwe]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rwa [← this]
  rw [← QuotientGroup.mk_mul, hc, QuotientGroup.mk_mul]

theorem conj_mem_oddIn {C : Subgroup G} {h d : G} (hh : h ∈ C) (hd : d ∈ oddIn C) :
    h * d * h⁻¹ ∈ oddIn C := by
  obtain ⟨d', hd', rfl⟩ := hd
  have hn : (pPrimeCore 2 ↥C).Normal := inferInstance
  exact ⟨⟨h, hh⟩ * d' * ⟨h, hh⟩⁻¹, hn.conj_mem d' hd' ⟨h, hh⟩, by simp⟩

theorem eq_of_le_oddIn_sup [Finite G] {C J K : Subgroup G} (hJC : J ≤ C) (hKC : K ≤ C)
    (hJ : IsPComponent 2 (J.subgroupOf C)) (hK : IsPComponent 2 (K.subgroupOf C))
    (hle : J ≤ oddIn C ⊔ K) : J = K := by
  by_contra hne
  have hKk : K ≤ coreActionKernel J := GSThmB.B5a.le_coreActionKernel_of_ne hJC hKC hJ hK hne
  have hOk : oddIn C ≤ coreActionKernel J := by
    intro o ho
    have hoN : o ∈ normalizer (J : Set G) :=
      UnbalancedCorr.pPrimeCore_le_normalizer_of_isPComponent hJC hJ ho
    have hoC : o ∈ C := by
      obtain ⟨o', -, rfl⟩ := ho
      exact o'.2
    refine mem_coreActionKernel.mpr ⟨hoN, fun j hj => ?_⟩
    have hD : J ⊓ oddIn C ≤ (pPrimeCore 2 J).map J.subtype := by
      refine le_map_pPrimeCore inf_le_left (fun h hh d hd => mem_inf.mpr ⟨?_, ?_⟩) ?_
      · exact mul_mem (mul_mem hh (mem_inf.mp hd).1) (inv_mem hh)
      · exact conj_mem_oddIn (hJC hh) (mem_inf.mp hd).2
      · exact Odd.of_dvd_nat (odd_card_map_pPrimeCore C)
          (Subgroup.card_dvd_of_le inf_le_right)
    refine hD (mem_inf.mpr ⟨?_, ?_⟩)
    · have h1 : o⁻¹ * j * o ∈ J := by
        have := (mem_normalizer_iff.mp (inv_mem hoN) j).mp hj
        rwa [inv_inv] at this
      rw [show j⁻¹ * o⁻¹ * j * o = j⁻¹ * (o⁻¹ * j * o) by group]
      exact mul_mem (inv_mem hj) h1
    · rw [show j⁻¹ * o⁻¹ * j * o = (j⁻¹ * o⁻¹ * j⁻¹⁻¹) * o by group]
      exact mul_mem (conj_mem_oddIn (inv_mem (hJC hj)) (inv_mem ho)) ho
  exact not_le_coreActionKernel_self hJC hJ (hle.trans (sup_le hOk hKk))

theorem gsFixedLayer_eq_self [Finite G] {a : G} {J : Subgroup G}
    (hJa : J ≤ centralizer ({a} : Set G))
    (hJ : IsPComponent 2 (J.subgroupOf (centralizer ({a} : Set G)))) : gsFixedLayer J a = J := by
  have hinf : J ⊓ centralizer ({a} : Set G) = J := inf_eq_left.mpr hJa
  unfold gsFixedLayer
  rw [hinf]
  exact pLayer_eq_self_of_isPComponent hJa hJ

theorem exists_conj_le_sylow [Finite G] {H : Subgroup G} (T : Sylow 2 G)
    (hTH : (T : Subgroup G) ≤ H) {V : Subgroup G} (hVH : V ≤ H) (hVp : IsPGroup 2 V) :
    ∃ h ∈ H, ∀ x ∈ V, h⁻¹ * x * h ∈ (T : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVp' : IsPGroup 2 (V.subgroupOf H) :=
    hVp.of_equiv (Subgroup.subgroupOfEquivOfLe hVH).symm
  obtain ⟨S, hS⟩ := hVp'.exists_le_sylow
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq H (T.subtype hTH) S
  refine ⟨h, h.2, fun x hx => ?_⟩
  have hxS : (⟨x, hVH hx⟩ : H) ∈ (S : Subgroup H) := hS hx
  rw [← hh, Sylow.smul_def, Sylow.pointwise_smul_def,
    Subgroup.mem_pointwise_smul_iff_inv_smul_mem, Sylow.coe_subtype,
    Subgroup.mem_subgroupOf] at hxS
  convert hxS using 1
  simp [MulAut.inv_def, MulAut.conj_symm_apply]

theorem centralizer_le_normalizer_of_solomon (hSol : SolomonFixedLayerStep) [Finite G]
    (hbase : L34BaseSetting G) {a : G} {J : Subgroup G} (ha : orderOf a = 2)
    (hJa : J ≤ centralizer ({a} : Set G))
    (hJ : IsPComponent 2 (J.subgroupOf (centralizer ({a} : Set G))))
    (hmax : GSWeakMaximalComponent J) (hL34 : IsL34Type (J ⧸ Open.fusionZStar J)) :
    centralizer ({a} : Set G) ≤ normalizer (J : Set G) := by
  obtain ⟨hsimple, hnab, hK, -, hUo, -, -, -⟩ := id hbase
  haveI := hsimple
  intro c hc
  have htop : GeneralizedFitting.subgroup G = ⊤ := GSLit.generalizedFitting_eq_top_of_simple
  let eF : GeneralizedFitting.subgroup G ≃* G :=
    (MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv
  have hsF : IsSimpleGroup (GeneralizedFitting.subgroup G) := eF.isSimpleGroup
  have hnF : ∃ u v : GeneralizedFitting.subgroup G, u * v ≠ v * u := by
    obtain ⟨u, v, huv⟩ := hnab
    exact ⟨eF.symm u, eF.symm v, fun h => huv (eF.symm.injective (by rw [map_mul, map_mul, h]))⟩
  have hoF : ¬ Blueprint.OddLieType (GeneralizedFitting.subgroup G) := fun h => hUo (Or.inl h)
  have hca : c⁻¹ * a * c = a := by
    have := mem_centralizer_singleton_iff.mp hc
    rw [mul_assoc, ← this, inv_mul_cancel_left]
  have hjc : ∀ j ∈ J, j * a = a * j := fun j hj => mem_centralizer_singleton_iff.mp (hJa hj)
  have haN : a ∈ normalizer (J : Set G) := by
    rw [mem_normalizer_iff]
    intro j
    constructor
    · intro hj
      rwa [show a * j * a⁻¹ = j by rw [← hjc j hj]; group]
    · intro hj
      have h1 := hjc _ hj
      have h2 : j = a * j * a⁻¹ := mul_left_cancel (a := a) (by rw [← h1]; group)
      rwa [h2]
  have h1 := hSol G hsF hnF hoF hK a J ha hJa hJ hmax hL34 hbase c (by rw [hca])
    (by rw [hca]; exact haN)
    (by
      rw [hca]
      intro j hj
      rw [show j⁻¹ * a⁻¹ * j * a = 1 by rw [mul_assoc, hjc j hj]; group]
      exact one_mem _)
  rw [hca, gsFixedLayer_eq_self hJa hJ] at h1
  obtain ⟨hJcC, hJcp⟩ := GSThmB.OddQuot.isPComponent_conjugate_subgroupOf hc hJa hJ
  have heq : J = conjugate J c := eq_of_le_oddIn_sup hJa hJcC hJ hJcp h1
  exact UnbalancedLayer.mem_normalizer_of_conjugate_eq heq.symm

theorem map_conj_inf_centralizer {T : Subgroup G} {x s : G} (hs : s ∈ T) :
    (T ⊓ centralizer ({x} : Set G)).map (MulAut.conj s⁻¹).toMonoidHom =
      T ⊓ centralizer ({s⁻¹ * x * s} : Set G) := by
  ext y
  simp only [mem_map, mem_inf, mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply, inv_inv]
  constructor
  · rintro ⟨z, ⟨hzT, hzx⟩, rfl⟩
    refine ⟨mul_mem (mul_mem (inv_mem hs) hzT) hs, ?_⟩
    calc s⁻¹ * z * s * (s⁻¹ * x * s) = s⁻¹ * (z * x) * s := by group
      _ = s⁻¹ * (x * z) * s := by rw [hzx]
      _ = s⁻¹ * x * s * (s⁻¹ * z * s) := by group
  · rintro ⟨hyT, hyx⟩
    refine ⟨s * y * s⁻¹, ⟨mul_mem (mul_mem hs hyT) (inv_mem hs), ?_⟩, by group⟩
    calc s * y * s⁻¹ * x = s * (y * (s⁻¹ * x * s)) * s⁻¹ := by group
      _ = s * ((s⁻¹ * x * s) * y) * s⁻¹ := by rw [hyx]
      _ = x * (s * y * s⁻¹) := by group

noncomputable def infCentralizerConjEquiv {T : Subgroup G} {x s : G} (hs : s ∈ T) :
    ↥(T ⊓ centralizer ({x} : Set G)) ≃* ↥(T ⊓ centralizer ({s⁻¹ * x * s} : Set G)) :=
  ((T ⊓ centralizer ({x} : Set G)).equivMapOfInjective _ (MulAut.conj s⁻¹).injective).trans
    (MulEquiv.subgroupCongr (map_conj_inf_centralizer hs))

theorem card_inf_centralizer_conj [Finite G] {T : Subgroup G} {x s : G} (hs : s ∈ T) :
    Nat.card ↥(T ⊓ centralizer ({s⁻¹ * x * s} : Set G)) =
      Nat.card ↥(T ⊓ centralizer ({x} : Set G)) :=
  (Nat.card_congr (infCentralizerConjEquiv hs).toEquiv).symm


theorem mem_normalizer_of_le_centralizer {a : G} {J : Subgroup G}
    (hJa : J ≤ centralizer ({a} : Set G)) : a ∈ normalizer (J : Set G) := by
  have hjc : ∀ j ∈ J, j * a = a * j := fun j hj => mem_centralizer_singleton_iff.mp (hJa hj)
  rw [mem_normalizer_iff]
  intro j
  constructor
  · intro hj
    rwa [show a * j * a⁻¹ = j by rw [← hjc j hj]; group]
  · intro hj
    have h1 := hjc _ hj
    have h2 : j = a * j * a⁻¹ := mul_left_cancel (a := a) (by rw [← h1]; group)
    rwa [h2]

theorem mem_coreActionKernel_of_le_centralizer {a : G} {J : Subgroup G}
    (hJa : J ≤ centralizer ({a} : Set G)) : a ∈ coreActionKernel J := by
  refine mem_coreActionKernel.mpr ⟨mem_normalizer_of_le_centralizer hJa, fun j hj => ?_⟩
  rw [show j⁻¹ * a⁻¹ * j * a = 1 by
    rw [mul_assoc, mem_centralizer_singleton_iff.mp (hJa hj)]; group]
  exact one_mem _

theorem mem_zStarIn_of_le_centralizer {a : G} {J : Subgroup G} (haJ : a ∈ J)
    (hJa : J ≤ centralizer ({a} : Set G)) : a ∈ zStarIn J := by
  refine ⟨⟨a, haJ⟩, ?_, rfl⟩
  show QuotientGroup.mk' (Open.fusionOddCore ↥J) ⟨a, haJ⟩ ∈ center _
  rw [mem_center_iff]
  intro q
  induction q using QuotientGroup.induction_on with
  | H j =>
  rw [QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  exact Subtype.ext (mem_centralizer_singleton_iff.mp (hJa j.2))

theorem isElemTwo_sup_zpowers [Finite G] {E : Subgroup G} {t : G} (hE : IsElemTwo E)
    (ht : t * t = 1) (htE : t ∉ E) (hc : ∀ e ∈ E, e * t = t * e) :
    IsElemTwo (E ⊔ zpowers t) ∧ Nat.card ↥(E ⊔ zpowers t) = 2 * Nat.card E := by
  have hcz : ∀ u ∈ E, ∀ v ∈ zpowers t, u * v = v * u := by
    intro u hu v hv
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hv
    exact (Commute.zpow_right (hc u hu) k)
  refine ⟨hE.sup (isElemTwo_zpowers ht) hcz, le_antisymm ?_ ?_⟩
  · have htN : t ∈ normalizer (E : Set G) :=
      mem_normalizer_of_le_centralizer fun e he => mem_centralizer_singleton_iff.mpr (hc e he)
    rw [sup_comm]
    exact card_zpowers_sup_le ht htN
  · have hlt : E < E ⊔ zpowers t := lt_of_le_of_ne le_sup_left fun h =>
      htE (h ▸ mem_sup_right (mem_zpowers t))
    obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hlt.le
    have hne : Nat.card E ≠ Nat.card ↥(E ⊔ zpowers t) := fun h =>
      hlt.ne (Subgroup.eq_of_le_of_card_ge hlt.le h.symm.le)
    have hpos : 0 < Nat.card E := Nat.card_pos
    rw [hk] at hne ⊢
    rcases k with _ | _ | k
    · simp at hk
      exact absurd hk Nat.card_pos.ne'
    · simp at hne
    · nlinarith

theorem isPGroup_of_isSylowTwoIn {S H : Subgroup G} (h : IsSylowTwoIn S H) : IsPGroup 2 S := by
  obtain ⟨hSH, P, hP⟩ := h
  have h1 := P.isPGroup'
  rw [hP] at h1
  exact h1.of_equiv (subgroupOfEquivOfLe hSH)

theorem eq_one_or_eq_of_mem_zpowers {u v : G} (hu : u * u = 1) (hv : v ∈ zpowers u) :
    v = 1 ∨ v = u := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hv
  have hu2 : u ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hu
  obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' k
  · left; rw [zpow_mul, hu2, one_zpow]
  · right; rw [zpow_add, zpow_mul, hu2, one_zpow, one_mul, zpow_one]

theorem mem_or_mul_of_mem_sup_zpowers {E : Subgroup G} {t v : G} (ht : t * t = 1)
    (hc : ∀ e ∈ E, e * t = t * e) (hv : v ∈ E ⊔ zpowers t) : v ∈ E ∨ ∃ e ∈ E, v = e * t := by
  have hle : zpowers t ≤ normalizer (E : Set G) := zpowers_le.mpr
    (mem_normalizer_of_le_centralizer fun e he => mem_centralizer_singleton_iff.mpr (hc e he))
  have hv' : v ∈ ((E : Set G) * (zpowers t : Set G)) := by
    rw [← coe_mul_of_right_le_normalizer_left E (zpowers t) hle]
    exact hv
  obtain ⟨e, he, u, hu, rfl⟩ := hv'
  rcases eq_one_or_eq_of_mem_zpowers ht hu with rfl | rfl
  · left; simpa using he
  · right; exact ⟨e, he, rfl⟩


end CFSG.ComponentClassification.GrSLit.GrS4
