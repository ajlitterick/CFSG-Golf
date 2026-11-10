module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalKProper
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalKernel
public import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancingLocal

open Subgroup CFSG.Assembly
open scoped commutatorElement

section Transport

variable {X Y : Type*} [Group X] [Group Y]

theorem map_centralizer_singleton_mulEquiv (e : X ≃* Y) (x : X) :
    (centralizer ({x} : Set X)).map e.toMonoidHom = centralizer ({e x} : Set Y) := by
  ext z
  rw [mem_map_equiv, mem_centralizer_singleton, mem_centralizer_singleton]
  constructor
  · intro h
    have h1 := congrArg e h
    rwa [map_mul, map_mul, e.apply_symm_apply] at h1
  · intro h
    apply e.injective
    rw [map_mul, map_mul, e.apply_symm_apply, h]

theorem map_pPrimeCore_centralizer_mulEquiv (p : ℕ) (e : X ≃* Y) (x : X) :
    ((pPrimeCore p (centralizer ({x} : Set X))).map (centralizer ({x} : Set X)).subtype).map
        e.toMonoidHom =
      (pPrimeCore p (centralizer ({e x} : Set Y))).map (centralizer ({e x} : Set Y)).subtype := by
  set C := centralizer ({x} : Set X)
  set C' := centralizer ({e x} : Set Y)
  let e' : C ≃* C' := (C.equivMapOfInjective e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr (map_centralizer_singleton_mulEquiv e x))
  have hcomm : e.toMonoidHom.comp C.subtype = C'.subtype.comp e'.toMonoidHom := by
    ext c
    rfl
  rw [map_map, hcomm, ← map_map, pPrimeCore_map_iso p e']

theorem map_pPrimeCore_centralizer_mulEquiv_of_eq (p : ℕ) (e : X ≃* Y) {x : X} {y : Y}
    (hxy : e x = y) :
    ((pPrimeCore p (centralizer ({x} : Set X))).map (centralizer ({x} : Set X)).subtype).map
        e.toMonoidHom =
      (pPrimeCore p (centralizer ({y} : Set Y))).map (centralizer ({y} : Set Y)).subtype := by
  subst hxy
  exact map_pPrimeCore_centralizer_mulEquiv p e x

end Transport

theorem centralizer_mk_eq_map_of_odd {H : Type*} [Group H] [Finite H] (R : Subgroup H)
    [R.Normal] (hR : Odd (Nat.card R)) {y : H} (hy : y ^ 2 = 1) :
    centralizer ({QuotientGroup.mk' R y} : Set (H ⧸ R)) =
      (centralizer ({y} : Set H)).map (QuotientGroup.mk' R) := by
  apply le_antisymm
  · intro q hq
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hA : IsPGroup 2 (zpowers y) := fun a => ⟨1, by
      obtain ⟨k, hk⟩ := mem_zpowers_iff.mp a.2
      apply Subtype.ext
      rw [Subgroup.coe_pow, pow_one, ← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
        zpow_natCast, hy, one_zpow, Subgroup.coe_one]⟩
    let act : zpowers y →* MulAut H := MulAut.conj.comp (zpowers y).subtype
    have hN : ∀ a : zpowers y, ∀ n ∈ R, act a n ∈ R := fun a n hn =>
      (inferInstance : R.Normal).conj_mem n hn a
    have hcop : ¬ 2 ∣ Nat.card R := fun h =>
      (Nat.not_even_iff_odd.mpr hR) (even_iff_two_dvd.mpr h)
    have hfix := Semidihedral.Principal.coprime_fixed_point_lifting 2 hA act R hN hcop
    have hq' : q ∈ {q : H ⧸ R | ∀ a : zpowers y,
        Semidihedral.Principal.CoprimeFixedPoint.quotientAction act R hN a q = q} := by
      intro a
      obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective R q
      obtain ⟨k, hk⟩ := mem_zpowers_iff.mp a.2
      have hc : Commute (QuotientGroup.mk' R h) (QuotientGroup.mk' R y) :=
        mem_centralizer_singleton.mp hq
      change QuotientGroup.mk' R ((a : H) * h * (a : H)⁻¹) = QuotientGroup.mk' R h
      rw [map_mul, map_mul, map_inv, ← hk, map_zpow, ((hc.zpow_right k).eq).symm,
        mul_inv_cancel_right]
    rw [hfix] at hq'
    obtain ⟨c, hc, hcq⟩ := hq'
    refine ⟨c, mem_centralizer_singleton.mpr ?_, hcq⟩
    have h1 : y * c * y⁻¹ = c := hc ⟨y, mem_zpowers y⟩
    calc c * y = (y * c * y⁻¹) * y := by rw [h1]
      _ = y * c := by group
  · rintro _ ⟨c, hc, rfl⟩
    have hc' : c * y = y * c := mem_centralizer_singleton.mp hc
    rw [mem_centralizer_singleton, ← map_mul, ← map_mul, hc']

theorem exists_central_sylow_two {X : Type*} [Group X] [Finite X] {t : X} (ht : t ^ 2 = 1)
    {E : Subgroup X} (hE : Odd (Nat.card E)) (htE : E ≤ centralizer ({t} : Set X))
    (hX : zpowers t ⊔ E = ⊤) : ∃ T : Sylow 2 X, (T : Subgroup X) ≤ center X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htc : t ∈ center X := by
    have hle : (⊤ : Subgroup X) ≤ centralizer ({t} : Set X) := by
      rw [← hX]
      exact sup_le (zpowers_le.mpr (mem_centralizer_singleton.mpr rfl)) htE
    exact mem_center_iff.mpr fun g => mem_centralizer_singleton.mp (hle (mem_top g))
  have hTc : zpowers t ≤ center X := zpowers_le.mpr htc
  have hTp : IsPGroup 2 (zpowers t) := fun a => ⟨1, by
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp a.2
    apply Subtype.ext
    rw [Subgroup.coe_pow, pow_one, ← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
      zpow_natCast, ht, one_zpow, Subgroup.coe_one]⟩
  have : (zpowers t).Normal := normal_of_le_center hTc
  have hidx : ¬ 2 ∣ (zpowers t).index := by
    have hmap : E.map (QuotientGroup.mk' (zpowers t)) = ⊤ := by
      have h1 := congrArg (map (QuotientGroup.mk' (zpowers t))) hX
      rwa [Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq,
        map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h1
    have h1 : (zpowers t).index ∣ Nat.card E := by
      rw [index_eq_card, ← card_top (G := X ⧸ zpowers t), ← hmap]
      exact card_map_dvd _ _
    intro h2
    exact (Nat.not_even_iff_odd.mpr hE) (even_iff_two_dvd.mpr (h2.trans h1))
  exact ⟨hTp.toSylow hidx, by rw [IsPGroup.toSylow_coe]; exact hTc⟩

theorem conjQuotAction_eq_one_iff_of_quotient {H : Type*} [Group H] (R : Subgroup H) [R.Normal]
    (LH : Subgroup H) [LH.Normal] [(LH.map (QuotientGroup.mk' R)).Normal] (O : Subgroup LH)
    [O.Characteristic] (hO : O = R.subgroupOf LH) (h : H) :
    conjQuotAction LH (centralPreimage O) h = 1 ↔
      conjQuotAction (LH.map (QuotientGroup.mk' R)) (center (LH.map (QuotientGroup.mk' R)))
        (QuotientGroup.mk' R h) = 1 := by
  set π := QuotientGroup.mk' R with hπ
  set Q := LH.map π with hQ
  have hcomm : ∀ a b : LH, ((⁅a, b⁆ : LH) : H) = ⁅(a : H), (b : H)⁆ := fun a b =>
    map_commutatorElement LH.subtype a b
  have key : ∀ m (hm : m ∈ LH),
      m ∈ (centralPreimage O).map LH.subtype ↔ π m ∈ (center Q).map Q.subtype := by
    intro m hm
    have h1 : m ∈ (centralPreimage O).map LH.subtype ↔ (⟨m, hm⟩ : LH) ∈ centralPreimage O :=
      ⟨fun ⟨z, hz, hzm⟩ => by rwa [show z = ⟨m, hm⟩ from Subtype.ext hzm] at hz,
        fun hz => ⟨_, hz, rfl⟩⟩
    have h2 : π m ∈ (center Q).map Q.subtype ↔ (⟨π m, mem_map_of_mem π hm⟩ : Q) ∈ center Q :=
      ⟨fun ⟨z, hz, hzm⟩ => by
        rwa [show z = ⟨π m, mem_map_of_mem π hm⟩ from Subtype.ext hzm] at hz,
        fun hz => ⟨_, hz, rfl⟩⟩
    rw [h1, h2, mem_centralPreimage_iff, mem_center_iff, hO]
    constructor
    · intro hc g
      obtain ⟨l, hl, hgl⟩ := g.2
      have h3 := hc ⟨l, hl⟩
      rw [mem_subgroupOf, hcomm, ← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply,
        map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h3
      apply Subtype.ext
      change (g : H ⧸ R) * π m = π m * (g : H ⧸ R)
      rw [← hgl]
      exact h3.symm
    · intro hc l
      have h5 := congrArg Subtype.val (hc ⟨π l, mem_map_of_mem π l.2⟩)
      rw [mem_subgroupOf, hcomm, ← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply,
        map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact h5.symm
  have hmemLH : ∀ l ∈ LH, ⁅l, h⁆ ∈ LH := fun l hl => by
    have heq : ⁅l, h⁆ = l * (h * l⁻¹ * h⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [heq]
    exact mul_mem hl ((inferInstance : LH.Normal).conj_mem _ (inv_mem hl) h)
  rw [conjQuotAction_eq_one_iff, conjQuotAction_eq_one_iff]
  constructor
  · intro h1 q hq
    obtain ⟨l, hl, rfl⟩ := hq
    rw [← map_commutatorElement]
    exact (key _ (hmemLH l hl)).mp (h1 l hl)
  · intro h1 l hl
    refine (key _ (hmemLH l hl)).mpr ?_
    rw [map_commutatorElement]
    exact h1 _ (mem_map_of_mem π hl)

theorem map_rangeRestrict_le_of_ker_eq {H M : Type*} [Group H] [Group M] (p : ℕ)
    (R : Subgroup H) [R.Normal] (P : Subgroup (H ⧸ R)) [P.Normal] (α : H →* M)
    (hker : α.ker = P.comap (QuotientGroup.mk' R)) (X : Subgroup H) (y : H)
    (hX : (X.map (QuotientGroup.mk' R)).map (QuotientGroup.mk' P) ≤
      (pPrimeCore p (centralizer {QuotientGroup.mk' P (QuotientGroup.mk' R y)})).map
        (centralizer {QuotientGroup.mk' P (QuotientGroup.mk' R y)}).subtype) :
    X.map α.rangeRestrict ≤
      (pPrimeCore p (centralizer {α.rangeRestrict y})).map
        (centralizer {α.rangeRestrict y}).subtype := by
  have hRker : R ≤ α.rangeRestrict.ker := by
    rw [MonoidHom.ker_rangeRestrict, hker]
    intro r hr
    change QuotientGroup.mk' R r ∈ P
    rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff r).mpr hr]
    exact one_mem _
  let ψ : H ⧸ R →* α.range := QuotientGroup.lift R α.rangeRestrict hRker
  have hψ : Function.Surjective ψ := by
    intro b
    obtain ⟨h, rfl⟩ := α.rangeRestrict_surjective b
    exact ⟨QuotientGroup.mk' R h, rfl⟩
  have hkerψ : ψ.ker = P := by
    rw [QuotientGroup.ker_lift, MonoidHom.ker_rangeRestrict, hker]
    exact map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective R) _
  let e : (H ⧸ R) ⧸ P ≃* α.range :=
    (QuotientGroup.quotientMulEquivOfEq hkerψ.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)
  have he : ∀ h : H, e (QuotientGroup.mk' P (QuotientGroup.mk' R h)) = α.rangeRestrict h :=
    fun h => rfl
  clear_value e
  have hecomp : (e.toMonoidHom.comp (QuotientGroup.mk' P)).comp (QuotientGroup.mk' R) =
      α.rangeRestrict := MonoidHom.ext he
  calc X.map α.rangeRestrict
      = ((X.map (QuotientGroup.mk' R)).map (QuotientGroup.mk' P)).map e.toMonoidHom := by
        rw [map_map, map_map, hecomp]
    _ ≤ _ := map_mono hX
    _ = _ := map_pPrimeCore_centralizer_mulEquiv_of_eq p e (he y)

theorem odd_two_quotient_core {H : Type*} [Group H] [Finite H] {LH DH : Subgroup H}
    [hLn : LH.Normal] (hQ : IsQuasisimple (LH ⧸ pPrimeCore 2 LH)) {yH : H} (hy : orderOf yH = 2)
    (hDy : DH ≤ centralizer {yH}) (hDn : (DH.subgroupOf (centralizer {yH})).Normal)
    (hDodd : Nat.Coprime 2 (Nat.card DH)) (hgen : LH ⊔ zpowers yH ⊔ DH = ⊤)
    (hLy : ⁅LH, zpowers yH⁆ = LH) (hLD : ⁅LH, DH⁆ = LH) :
    (conjQuotAction LH (centralPreimage (pPrimeCore 2 LH))).ker =
        (pCore 2 (H ⧸ pPrimeCore 2 H)).comap (QuotientGroup.mk' (pPrimeCore 2 H)) ∧
      (DH.map (QuotientGroup.mk' (pPrimeCore 2 H))).map
          (QuotientGroup.mk' (pCore 2 (H ⧸ pPrimeCore 2 H))) ≤
        (pPrimeCore 2 (centralizer {(QuotientGroup.mk' (pCore 2 (H ⧸ pPrimeCore 2 H))
          (QuotientGroup.mk' (pPrimeCore 2 H) yH))})).map
          (centralizer {(QuotientGroup.mk' (pCore 2 (H ⧸ pPrimeCore 2 H))
            (QuotientGroup.mk' (pPrimeCore 2 H) yH))}).subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := pPrimeCore 2 H with hRdef
  set π := QuotientGroup.mk' R with hπdef
  have hQn : (LH.map π).Normal := hLn.map π (QuotientGroup.mk'_surjective R)
  have hRodd : Odd (Nat.card R) := Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hLHsub : LH.IsSubnormal := hLn.isSubnormal
  have hQq : IsQuasisimple (LH.map π) := LocalCores.isQuasisimple_of_mulEquiv
    (CatalogueBHeldSmallCore.subnormalCoreQuotientEquivImage 2 LH hLHsub) hQ
  have hQne : LH.map π ≠ ⊥ :=
    (nontrivial_iff_ne_bot (LH.map π)).mp (LocalCores.isQuasisimple_nontrivial hQq)
  have hcoreK : pPrimeCore 2 (H ⧸ R) = ⊥ := pPrimeCore_quotient_pPrimeCore_eq_bot 2
  have hy2 : yH ^ 2 = 1 := by
    rw [← hy]
    exact pow_orderOf_eq_one yH
  have hy₀ : orderOf (π yH) = 2 := by
    refine orderOf_eq_prime (by rw [← map_pow, hy2, map_one]) fun h1 => ?_
    have hyR : yH ∈ R := by
      rw [hπdef, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact h1
    have h2 : orderOf yH ∣ Nat.card R := Subgroup.orderOf_dvd_natCard R hyR
    rw [hy] at h2
    exact (Nat.not_even_iff_odd.mpr hRodd) (even_iff_two_dvd.mpr h2)
  have hD₀odd : Nat.Coprime 2 (Nat.card (DH.map π)) :=
    hDodd.coprime_dvd_right (card_map_dvd _ _)
  have hD₀c : DH.map π ≤ centralizer {π yH} := by
    rintro _ ⟨d, hd, rfl⟩
    rw [mem_centralizer_singleton, ← map_mul, ← map_mul, mem_centralizer_singleton.mp (hDy hd)]
  have hcentK : centralizer {π yH} = (centralizer {yH}).map π :=
    centralizer_mk_eq_map_of_odd R hRodd hy2
  have hD₀n : ((DH.map π).subgroupOf (centralizer {π yH})).Normal := by
    rw [hcentK]
    exact map_subgroupOf_normal π hDn hDy
  have hKgen : LH.map π ⊔ DH.map π ⊔ zpowers (π yH) = ⊤ := by
    have h1 := congrArg (map π) hgen
    rwa [Subgroup.map_sup, Subgroup.map_sup, MonoidHom.map_zpowers,
      map_top_of_surjective π (QuotientGroup.mk'_surjective R), sup_right_comm] at h1
  have hQy : ⁅LH.map π, zpowers (π yH)⁆ = LH.map π := by
    rw [← MonoidHom.map_zpowers, ← map_commutator, hLy]
  have hQD : ⁅LH.map π, DH.map π⁆ = LH.map π := by
    rw [← map_commutator, hLD]
  have hT : ∃ T : Sylow 2 ((H ⧸ R) ⧸ LH.map π),
      (T : Subgroup ((H ⧸ R) ⧸ LH.map π)) ≤ center _ := by
    refine exists_central_sylow_two (t := QuotientGroup.mk' (LH.map π) (π yH))
      (E := (DH.map π).map (QuotientGroup.mk' (LH.map π))) ?_ ?_ ?_ ?_
    · rw [← map_pow, ← map_pow, hy2, map_one, map_one]
    · exact Nat.coprime_two_left.mp (hD₀odd.coprime_dvd_right (card_map_dvd _ _))
    · rintro _ ⟨d, hd, rfl⟩
      rw [mem_centralizer_singleton, ← map_mul, ← map_mul,
        mem_centralizer_singleton.mp (hD₀c hd)]
    · have h1 := congrArg (map (QuotientGroup.mk' (LH.map π))) hKgen
      rwa [Subgroup.map_sup, Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq,
        MonoidHom.map_zpowers, map_top_of_surjective _ (QuotientGroup.mk'_surjective (LH.map π)),
        sup_comm] at h1
  have hkernel := corefree_quasisimple_small_quotient_action_kernel
    (K := H ⧸ R) hcoreK (Q := LH.map π) hQq hT
  have hker : (conjQuotAction LH (centralPreimage (pPrimeCore 2 LH))).ker =
      (pCore 2 (H ⧸ R)).comap π := by
    ext h
    rw [MonoidHom.mem_ker, mem_comap, ← hkernel.2.2.2.2, MonoidHom.mem_ker]
    exact conjQuotAction_eq_one_iff_of_quotient R LH (pPrimeCore 2 LH)
      (CatalogueBHeldSmallCore.primeCore_subnormal_intersection 2 LH hLHsub) h
  exact ⟨hker, (SmallLocal.odd_centralizer_core_survives_centralized_prime_core
    (K := H ⧸ R) (Q := LH.map π) (P := pCore 2 (H ⧸ R)) (D := DH.map π)
    Nat.prime_two hQne (pCore_isPGroup (p := 2) (G := H ⧸ R)) hkernel.2.1 hy₀ hD₀c hD₀n hD₀odd
    hKgen hQy hQD).2.2.1⟩

theorem ne_bot_of_le_map_subtype {X : Type*} [Group X] {C : Subgroup X} {K : Subgroup C}
    {A : Subgroup X} (hA : A ≠ ⊥) (hle : A ≤ K.map C.subtype) : K ≠ ⊥ := by
  rintro rfl
  rw [Subgroup.map_bot, le_bot_iff] at hle
  exact hA hle


variable {G : Type} [Group G]

theorem hull_sup_eq_top (L D : Subgroup G) (y : G) :
    L.subgroupOf (hull L y D) ⊔ zpowers (⟨y, mem_hull_elem L y D⟩ : hull L y D) ⊔
      D.subgroupOf (hull L y D) = ⊤ := by
  apply map_injective (hull L y D).subtype_injective
  rw [Subgroup.map_sup, Subgroup.map_sup, map_subtype_subgroupOf (le_hull_left L y D),
    MonoidHom.map_zpowers,
    map_subtype_subgroupOf (le_hull_right L y D), ← MonoidHom.range_eq_map, range_subtype]
  rfl


end CFSG.ComponentClassification.UnbalancingLocal
