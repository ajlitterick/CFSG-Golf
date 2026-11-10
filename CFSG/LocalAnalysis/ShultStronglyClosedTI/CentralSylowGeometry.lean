module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.NormalGraphFusion

public section

namespace CFSG.ShultStronglyClosedTI.NormalGraph

variable {G : Type*} [Group G]

theorem map_centralizer_equiv (z : G) (e : G ≃* G) :
    (Subgroup.centralizer ({z} : Set G)).map e.toMonoidHom =
      Subgroup.centralizer ({e z} : Set G) := by
  ext x
  constructor
  · rintro ⟨c, hc, rfl⟩
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    change e c * e z = e z * e c
    simpa only [map_mul] using congrArg e (Subgroup.mem_centralizer_singleton_iff.mp hc)
  · intro hx
    refine Subgroup.mem_map.mpr ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    have h := congrArg e.symm (Subgroup.mem_centralizer_singleton_iff.mp hx)
    simpa only [map_mul, MulEquiv.symm_apply_apply] using h

theorem centralizer_card_eq_of_isConj {z a : G} (hconj : IsConj z a) :
    Nat.card (Subgroup.centralizer ({z} : Set G)) =
      Nat.card (Subgroup.centralizer ({a} : Set G)) := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp hconj
  change Nat.card (Subgroup.centralizer ({z} : Set G)) =
    Nat.card (Subgroup.centralizer ({(MulAut.conj g) z} : Set G))
  rw [← map_centralizer_equiv z (MulAut.conj g)]
  exact (Subgroup.card_map_of_injective (MulAut.conj g).injective).symm

theorem index_two_le (H K L : Subgroup G)
    (hindex : (H.subgroupOf K).index = 2) {t : G} (htK : t ∈ K) (htH : t ∉ H)
    (hHL : H ≤ L) (htL : t ∈ L) : K ≤ L := by
  intro k hk
  by_cases hkH : k ∈ H
  · exact hHL hkH
  · have htinv : t⁻¹ ∉ H := by
      intro h
      exact htH (by simpa only [inv_inv] using H.inv_mem h)
    have hprod : k * t⁻¹ ∈ H := by
      have h := (Subgroup.mul_mem_iff_of_index_two hindex
        (a := (⟨k, hk⟩ : K)) (b := (⟨t, htK⟩ : K)⁻¹)).mpr
          (by change (k ∈ H ↔ t⁻¹ ∈ H); simp only [hkH, htinv])
      exact h
    have hmem := L.mul_mem (hHL hprod) htL
    simpa only [inv_mul_cancel_right] using hmem

variable [Finite G]

theorem exists_normal_index_two_extension (H : Subgroup G) (n : ℕ)
    (hcard : Nat.card H = 2 ^ n) (hdiv : 2 ^ (n + 1) ∣ Nat.card G) :
    ∃ K : Subgroup G, H ≤ K ∧ K ≤ Subgroup.normalizer (H : Set G) ∧
      Nat.card K = 2 * Nat.card H ∧ (H.subgroupOf K).index = 2 ∧ IsPGroup 2 K := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let N := Subgroup.normalizer (H : Set G)
  have hNdiv : 2 ^ (n + 1) ∣ Nat.card N :=
    Sylow.prime_pow_dvd_card_normalizer hdiv hcard
  have hHNcard : Nat.card (H.subgroupOf N) = 2 ^ n :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe H.le_normalizer).toEquiv).trans hcard
  obtain ⟨K', hK'card, hHK'⟩ := Sylow.exists_subgroup_card_pow_succ hNdiv hHNcard
  let K := K'.map N.subtype
  have hHK : H ≤ K := by
    intro h hh
    exact Subgroup.mem_map_of_mem N.subtype (hHK' (show (⟨h, H.le_normalizer hh⟩ : N) ∈
      H.subgroupOf N from hh))
  have hKN : K ≤ N := by
    rintro _ ⟨x, _, rfl⟩
    exact x.property
  have hKcard : Nat.card K = 2 * Nat.card H := by
    rw [Subgroup.card_map_of_injective N.subtype_injective, hK'card, hcard, pow_succ']
  have hindex : (H.subgroupOf K).index = 2 := by
    rw [Subgroup.index_eq_card_div, hKcard,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHK).toEquiv]
    exact Nat.mul_div_cancel 2 Nat.card_pos
  have hKtwo : IsPGroup 2 K :=
    IsPGroup.of_card (n := n + 1) (by rw [hKcard, hcard, pow_succ'])
  exact ⟨K, hHK, hKN, hKcard, hindex, hKtwo⟩

omit [Finite G] in
theorem centralizer_sylow_contains (z : G) (hz : orderOf z = 2)
    (S : Sylow 2 (Subgroup.centralizer ({z} : Set G))) :
    z ∈ (S : Subgroup (Subgroup.centralizer ({z} : Set G))).map
      (Subgroup.centralizer ({z} : Set G)).subtype := by
  let C := Subgroup.centralizer ({z} : Set G)
  have hzC : z ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  let zC : C := ⟨z, hzC⟩
  have hzcenter : zC ∈ Subgroup.center C := by
    apply Subgroup.mem_center_iff.mpr
    intro c
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp c.property
  let : (Subgroup.zpowers zC).Normal :=
    Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hzcenter)
  have hcyc : IsPGroup 2 (Subgroup.zpowers zC) := IsPGroup.of_card (n := 1)
    (by rw [Nat.card_zpowers, Subgroup.orderOf_mk, hz, pow_one])
  have hmem : zC ∈ (S : Subgroup C) := hcyc.le_sylow_of_normal S (Subgroup.mem_zpowers zC)
  exact Subgroup.mem_map_of_mem C.subtype hmem

theorem centralizer_two_subgroup_card_le (z a : G)
    (S : Sylow 2 (Subgroup.centralizer ({z} : Set G)))
    (K : Subgroup G) (hKtwo : IsPGroup 2 K)
    (hKcentral : K ≤ Subgroup.centralizer ({a} : Set G)) (hconj : IsConj z a) :
    Nat.card K ≤ Nat.card
      ((S : Subgroup (Subgroup.centralizer ({z} : Set G))).map
        (Subgroup.centralizer ({z} : Set G)).subtype) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let C := Subgroup.centralizer ({a} : Set G)
  have hK'Ctwo : IsPGroup 2 (K.subgroupOf C) :=
    hKtwo.of_equiv (Subgroup.subgroupOfEquivOfLe hKcentral).symm
  obtain ⟨P, hP⟩ := hK'Ctwo.exists_le_sylow
  have hcard := Subgroup.card_le_of_le hP
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKcentral).toEquiv,
    P.card_eq_multiplicity] at hcard
  have hCcard := centralizer_card_eq_of_isConj hconj
  change Nat.card (Subgroup.centralizer ({z} : Set G)) = Nat.card C at hCcard
  rw [← hCcard, ← S.card_eq_multiplicity] at hcard
  simpa only [Subgroup.card_map_of_injective
    (Subgroup.centralizer ({z} : Set G)).subtype_injective] using hcard

omit [Finite G] in
theorem conj_eq_iff_centralizer (t z : G) :
    (MulAut.conj t) z = z ↔ t ∈ Subgroup.centralizer ({z} : Set G) := by
  constructor
  · intro h
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    have h' := congrArg (fun x : G => x * t) h
    simpa only [MulAut.conj_apply, mul_assoc, inv_mul_cancel, mul_one] using h'
  · intro h
    change t * z * t⁻¹ = z
    rw [Subgroup.mem_centralizer_singleton_iff.mp h]
    group

theorem centralizer_sylow_no_extra_two_factor (D : Set G)
    (horder : ∀ x ∈ D, orderOf x = 2)
    (hconj : ∀ x ∈ D, ∀ g : G, (MulAut.conj g) x ∈ D)
    (hproduct : ∀ x ∈ D, ∀ y ∈ D, x ≠ y → Commute x y → x * y ∈ D)
    (hdisconnected : ¬ (graph D horder).Preconnected) (z : D)
    (S : Sylow 2 (Subgroup.centralizer ({(z : G)} : Set G))) :
    let H := (S : Subgroup (Subgroup.centralizer ({(z : G)} : Set G))).map
      (Subgroup.centralizer ({(z : G)} : Set G)).subtype
    ∀ n : ℕ, Nat.card H = 2 ^ n → ¬ 2 ^ (n + 1) ∣ Nat.card G := by
  let C := Subgroup.centralizer ({(z : G)} : Set G)
  let H := (S : Subgroup C).map C.subtype
  change ∀ n : ℕ, Nat.card H = 2 ^ n → ¬ 2 ^ (n + 1) ∣ Nat.card G
  intro n hHcard hdiv
  have hzH : (z : G) ∈ H := centralizer_sylow_contains (z : G) (horder z z.property) S
  have hHC : H ≤ C := by
    rintro _ ⟨s, _, rfl⟩
    exact s.property
  obtain ⟨R, hHR, hRN, hRcard, hindex, hRtwo⟩ :=
    exists_normal_index_two_extension H n hHcard hdiv
  have hRnotH : ¬ R ≤ H := by
    intro hRH
    have hle := Subgroup.card_le_of_le hRH
    have hpos : 0 < Nat.card H := Nat.card_pos
    omega
  obtain ⟨t, htR, htH⟩ := IsConcreteLE.not_le_iff_exists.mp hRnotH
  have htN : t ∈ Subgroup.normalizer (H : Set G) := hRN htR
  by_cases hfixed : (MulAut.conj t) (z : G) = z
  · have hRC : R ≤ C := index_two_le H R C hindex htR htH hHC
      ((conj_eq_iff_centralizer t z).mp hfixed)
    have hle := centralizer_two_subgroup_card_le (z : G) (z : G) S R hRtwo hRC
      (IsConj.refl _)
    change Nat.card R ≤ Nat.card H at hle
    have hpos : 0 < Nat.card H := Nat.card_pos
    omega
  · let zt := (MulAut.conj t) (z : G)
    have hztD : zt ∈ D := hconj z z.property t
    have hHzt : H ≤ Subgroup.centralizer ({zt} : Set G) := by
      have hmap : H.map (MulAut.conj t).toMonoidHom = H :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp htN
      have hle := Subgroup.map_mono (f := (MulAut.conj t).toMonoidHom) hHC
      rw [hmap, map_centralizer_equiv] at hle
      exact hle
    have hzz : Commute (z : G) zt := Subgroup.mem_centralizer_singleton_iff.mp (hHzt hzH)
    have hzne : (z : G) ≠ zt := fun h => hfixed h.symm
    let a := (z : G) * zt
    have haD : a ∈ D := hproduct z z.property zt hztD hzne hzz
    have hHCa : H ≤ Subgroup.centralizer ({a} : Set G) := by
      intro s hs
      apply Subgroup.mem_centralizer_singleton_iff.mpr
      have hsz : Commute s (z : G) := Subgroup.mem_centralizer_singleton_iff.mp (hHC hs)
      have hszt : Commute s zt := Subgroup.mem_centralizer_singleton_iff.mp (hHzt hs)
      exact (hsz.mul_right hszt).eq
    have htSqH : t ^ 2 ∈ H :=
      (H.subgroupOf R).sq_mem_of_index_two hindex (⟨t, htR⟩ : R)
    have htwice : (MulAut.conj t) zt = (z : G) := by
      have h := (conj_eq_iff_centralizer (t ^ 2) z).mpr (hHC htSqH)
      calc
        (MulAut.conj t) zt = (MulAut.conj (t ^ 2)) (z : G) := by
          dsimp only [zt]
          simp only [MulAut.conj_apply, pow_two, mul_inv_rev]
          group
        _ = (z : G) := h
    have htCa : t ∈ Subgroup.centralizer ({a} : Set G) := by
      apply (conj_eq_iff_centralizer t a).mp
      change (MulAut.conj t) ((z : G) * zt) = (z : G) * zt
      rw [map_mul, htwice]
      exact hzz.eq.symm
    have hRCa : R ≤ Subgroup.centralizer ({a} : Set G) :=
      index_two_le H R _ hindex htR htH hHCa htCa
    have haz : IsConj (z : G) a :=
      conjugacy_transitive D horder hconj hproduct hdisconnected z ⟨a, haD⟩
    have hle := centralizer_two_subgroup_card_le (z : G) a S R hRtwo hRCa haz
    change Nat.card R ≤ Nat.card H at hle
    have hpos : 0 < Nat.card H := Nat.card_pos
    omega

theorem centralizer_sylow_is_global (D : Set G)
    (horder : ∀ x ∈ D, orderOf x = 2)
    (hconj : ∀ x ∈ D, ∀ g : G, (MulAut.conj g) x ∈ D)
    (hproduct : ∀ x ∈ D, ∀ y ∈ D, x ≠ y → Commute x y → x * y ∈ D)
    (hdisconnected : ¬ (graph D horder).Preconnected) (z : D)
    (S : Sylow 2 (Subgroup.centralizer ({(z : G)} : Set G))) :
    ∃ T : Sylow 2 G, (T : Subgroup G) =
      (S : Subgroup (Subgroup.centralizer ({(z : G)} : Set G))).map
        (Subgroup.centralizer ({(z : G)} : Set G)).subtype := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let C := Subgroup.centralizer ({(z : G)} : Set G)
  let H := (S : Subgroup C).map C.subtype
  have hHtwo : IsPGroup 2 H := S.isPGroup'.map C.subtype
  obtain ⟨n, hcard⟩ := hHtwo.exists_card_eq
  have hno : ¬ 2 ∣ H.index := by
    intro hindex
    apply centralizer_sylow_no_extra_two_factor D horder hconj hproduct hdisconnected z S n hcard
    rw [← H.card_mul_index, hcard, pow_succ]
    exact Nat.mul_dvd_mul_left _ hindex
  exact ⟨hHtwo.toSylow hno, rfl⟩

theorem exists_central_sylow (D : Set G)
    (horder : ∀ x ∈ D, orderOf x = 2)
    (hconj : ∀ x ∈ D, ∀ g : G, (MulAut.conj g) x ∈ D)
    (hproduct : ∀ x ∈ D, ∀ y ∈ D, x ≠ y → Commute x y → x * y ∈ D)
    (hdisconnected : ¬ (graph D horder).Preconnected) (z : D) :
    ∃ T : Sylow 2 G, ∃ hzT : (z : G) ∈ (T : Subgroup G),
      (⟨(z : G), hzT⟩ : (T : Subgroup G)) ∈ Subgroup.center (T : Subgroup G) := by
  let S := (inferInstance : Nonempty (Sylow 2
    (Subgroup.centralizer ({(z : G)} : Set G)))).some
  obtain ⟨T, hT⟩ := centralizer_sylow_is_global D horder hconj hproduct hdisconnected z S
  have hzT : (z : G) ∈ (T : Subgroup G) :=
    hT.symm ▸ centralizer_sylow_contains (z : G) (horder z z.property) S
  refine ⟨T, hzT, Subgroup.mem_center_iff.mpr ?_⟩
  intro t
  apply Subtype.ext
  have htC : (t : G) ∈ Subgroup.centralizer ({(z : G)} : Set G) := by
    have ht : (t : G) ∈ (S : Subgroup
        (Subgroup.centralizer ({(z : G)} : Set G))).map
          (Subgroup.centralizer ({(z : G)} : Set G)).subtype := by
      rw [← hT]
      exact t.property
    obtain ⟨s, _, hs⟩ := Subgroup.mem_map.mp ht
    exact hs ▸ s.property
  exact Subgroup.mem_centralizer_singleton_iff.mp htC


end CFSG.ShultStronglyClosedTI.NormalGraph
