module

public import CFSG.LocalAnalysis.SeitzReduction.FoursGroupExceptionalBasic
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotZStar

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Open CFSG.EvenSmallLie CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977

section SylowOrderTwo

variable {C : Type*} [Group C] [Finite C]

theorem odd_card_pPrimeCore_two : Odd (Nat.card (pPrimeCore 2 C)) :=
  Nat.coprime_two_left.1 (pPrimeCore_coprime_card (p := 2) (G := C))

theorem index_pPrimeCore_two_eq_two (S : Sylow 2 C) (hS : Nat.card S = 2) :
    (pPrimeCore 2 C).index = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, ⟨-, -, hidx, -⟩, -⟩ :=
    cyclic_sylow_normal_odd_complement S (isCyclic_of_prime_card hS)
  rw [hidx, hS]

theorem mem_pPrimeCore_two_iff_odd_orderOf (S : Sylow 2 C) (hS : Nat.card S = 2) (y : C) :
    y ∈ pPrimeCore 2 C ↔ Odd (orderOf y) := by
  constructor
  · intro hy
    exact Odd.of_dvd_nat odd_card_pPrimeCore_two (Subgroup.orderOf_dvd_natCard _ hy)
  · rintro ⟨k, hk⟩
    have hy2 : (y ^ (k + 1)) ^ 2 = y := by
      rw [← pow_mul, show (k + 1) * 2 = orderOf y + 1 by omega, pow_succ, pow_orderOf_eq_one,
        one_mul]
    rw [← hy2]
    exact sq_mem_of_index_two (index_pPrimeCore_two_eq_two S hS) _

end SylowOrderTwo

section Zpowers

variable {G : Type*} [Group G]

theorem eq_one_or_eq_of_mem_zpowers {t y : G} (ht : orderOf t = 2) (hy : y ∈ zpowers t) :
    y = 1 ∨ y = t := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
  rw [← zpow_mod_orderOf, ht]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [Nat.cast_ofNat, h, zpow_zero]
  · right
    rw [Nat.cast_ofNat, h, zpow_one]

end Zpowers

section Standard

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem exists_orderOf_eq_two_mem_centralizer (hset : StandardSetting G L) :
    ∃ t ∈ centralizer (L : Set G), orderOf t = 2 := by
  have h2 : 2 ∣ Nat.card (centralizer (L : Set G)) := even_iff_two_dvd.1 hset.standard.2.1
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 2 h2
  exact ⟨u, u.2, by rwa [orderOf_coe]⟩

theorem conj_eq_inv_of_odd_of_standard (hset : StandardSetting G L)
    (hsyl : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) :
    (∀ x ∈ centralizer (L : Set G), Odd (orderOf x) → t * x * t⁻¹ = x⁻¹) ∧
      ∀ x ∈ centralizer (L : Set G), ∀ y ∈ centralizer (L : Set G), Odd (orderOf x) →
        Odd (orderOf y) → x * y = y * x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer (L : Set G) with hCdef
  obtain ⟨S, -⟩ := hset.cyclic
  have hS := hsyl S
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  set A : Subgroup G := (pPrimeCore 2 C).map C.subtype with hAdef
  have hmemA : ∀ x : G, x ∈ A ↔ x ∈ C ∧ Odd (orderOf x) := by
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.2, ?_⟩
      rw [coe_subtype, orderOf_coe]
      exact (mem_pPrimeCore_two_iff_odd_orderOf S hS y).1 hy
    · rintro ⟨hxC, hxo⟩
      exact ⟨⟨x, hxC⟩, (mem_pPrimeCore_two_iff_odd_orderOf S hS _).2 (by rwa [orderOf_mk]), rfl⟩
  have hAodd : Odd (Nat.card A) := by
    rw [hAdef, card_map_of_injective C.subtype_injective]
    exact odd_card_pPrimeCore_two
  have hCtN : centralizer ({t} : Set G) ≤ normalizer (L : Set G) :=
    centralizer_le_normalizer_of_standard hset.standard htC ht
  have hAt : ∀ x ∈ A, t * x * t⁻¹ = x → x = 1 := by
    intro x hxA hxt
    set H := centralizer ({t} : Set G) with hHdef
    set B : Subgroup H := (A ⊓ H).subgroupOf H with hBdef
    have hBn : B.Normal := by
      refine ⟨fun b hb c => ?_⟩
      rw [hBdef, mem_subgroupOf, mem_inf] at hb ⊢
      refine ⟨?_, (c * b * c⁻¹).2⟩
      have hbA := (hmemA _).1 hb.1
      rw [hmemA]
      refine ⟨?_, ?_⟩
      · simpa using conj_mem_centralizer_of_mem_normalizer (hCtN c.2) hbA.1
      · have h := MulEquiv.orderOf_eq (MulAut.conj (c : G)) (b : G)
        rw [MulAut.conj_apply] at h
        simpa [h] using hbA.2
    have hBodd : Odd (Nat.card B) := by
      rw [hBdef, Nat.card_congr (subgroupOfEquivOfLe (inf_le_right : A ⊓ H ≤ H)).toEquiv]
      exact Odd.of_dvd_nat hAodd (card_dvd_of_le inf_le_left)
    have hBle : B ≤ standardComponentOddCore H := le_sSup ⟨hBn, hBodd⟩
    rw [hset.core t ht, le_bot_iff] at hBle
    have hxH : x ∈ H := by
      rw [hHdef, mem_centralizer_singleton_iff]
      calc x * t = (t * x * t⁻¹) * t := by rw [hxt]
        _ = t * x := by group
    have hxB : (⟨x, hxH⟩ : H) ∈ B := mem_subgroupOf.2 ⟨hxA, hxH⟩
    rw [hBle, mem_bot] at hxB
    exact congrArg Subtype.val hxB
  have hAconj : ∀ x ∈ A, t * x * t⁻¹ ∈ A := by
    intro x hx
    rw [hmemA] at hx ⊢
    refine ⟨C.mul_mem (C.mul_mem htC hx.1) (C.inv_mem htC), ?_⟩
    have h := MulEquiv.orderOf_eq (MulAut.conj t) x
    rw [MulAut.conj_apply] at h
    rw [h]
    exact hx.2
  let φ : A →* A :=
    ((MulAut.conj t).toMonoidHom.domRestrict A).codRestrict A fun x => hAconj x x.2
  have hφ : ∀ x : A, ((φ x : A) : G) = t * x * t⁻¹ := fun x => rfl
  have hfpf : MonoidHom.FixedPointFree φ := fun x hx =>
    Subtype.ext (hAt x x.2 (by rw [← hφ, hx]))
  have hinv : Function.Involutive φ := fun x => by
    apply Subtype.ext
    rw [hφ, hφ]
    calc t * (t * (x : G) * t⁻¹) * t⁻¹ = (t * t) * x * (t * t)⁻¹ := by group
      _ = x := by rw [htt, one_mul, inv_one, mul_one]
  have hφinv := hfpf.coe_eq_inv_of_involutive hinv
  refine ⟨fun x hxC hxo => ?_, fun x hxC y hyC hxo hyo => ?_⟩
  · have hxA : x ∈ A := (hmemA x).2 ⟨hxC, hxo⟩
    have h := congrArg (fun f : A → A => ((f ⟨x, hxA⟩ : A) : G)) hφinv
    simpa [hφ] using h
  · have hxA : x ∈ A := (hmemA x).2 ⟨hxC, hxo⟩
    have hyA : y ∈ A := (hmemA y).2 ⟨hyC, hyo⟩
    exact congrArg Subtype.val (hfpf.commute_all_of_involutive hinv ⟨x, hxA⟩ ⟨y, hyA⟩).eq

theorem exists_odd_conj_eq_of_orderOf_eq_two (hset : StandardSetting G L)
    (hsyl : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {t u : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (huC : u ∈ centralizer (L : Set G)) (hu : orderOf u = 2) :
    ∃ c ∈ centralizer (L : Set G), Odd (orderOf c) ∧ c * t * c⁻¹ = u := by
  set C := centralizer (L : Set G) with hCdef
  obtain ⟨S, -⟩ := hset.cyclic
  have hS := hsyl S
  have hidx := index_pPrimeCore_two_eq_two S hS
  have hinv := (conj_eq_inv_of_odd_of_standard hset hsyl htC ht).1
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have hnot : ∀ (v : C), orderOf (v : G) = 2 → v ∉ pPrimeCore 2 C := fun v hv hvA => by
    rw [mem_pPrimeCore_two_iff_odd_orderOf S hS, ← orderOf_coe, hv] at hvA
    exact absurd hvA (by decide)
  have hut : (⟨u, huC⟩ : C) * ⟨t, htC⟩ ∈ pPrimeCore 2 C :=
    (mul_mem_iff_of_index_two hidx).2 (iff_of_false (hnot _ hu) (hnot _ ht))
  rw [mem_pPrimeCore_two_iff_odd_orderOf S hS, ← orderOf_coe] at hut
  set a := u * t with ha
  have haC : a ∈ C := C.mul_mem huC htC
  have hao : Odd (orderOf a) := hut
  obtain ⟨k, hk⟩ := hao
  set c := a ^ (k + 1) with hc
  have hcC : c ∈ C := C.pow_mem haC _
  have hco : Odd (orderOf c) := Odd.of_dvd_nat ⟨k, hk⟩ (orderOf_pow_dvd _)
  have hc2 : c * c = a := by
    rw [hc, ← sq, ← pow_mul, show (k + 1) * 2 = orderOf a + 1 by omega, pow_succ,
      pow_orderOf_eq_one, one_mul]
  have htc : t * c * t⁻¹ = c⁻¹ := hinv c hcC hco
  refine ⟨c, hcC, hco, ?_⟩
  calc c * t * c⁻¹ = c * (t * c * t⁻¹)⁻¹ * t := by group
    _ = c * c * t := by rw [htc, inv_inv]
    _ = a * t := by rw [hc2]
    _ = u := by rw [ha, mul_assoc, htt, mul_one]


theorem kernel (hset : StandardSetting G L) (hZ : center L = ⊥)
    (hI : HypothesisOne (L ⧸ center L)) :
    ∃ t : G, orderOf t = 2 ∧ t ∈ centralizer (L : Set G) ∧
      (∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) ∧
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t ∧
      centralizer ({t} : Set G) ≤ normalizer (L : Set G) ∧
      (∀ u ∈ centralizer (L : Set G), orderOf u = 2 →
        ∃ c ∈ centralizer (L : Set G), Odd (orderOf c) ∧ c * t * c⁻¹ = u) ∧
      ∀ x ∈ centralizer (L : Set G), Odd (orderOf x) → t * x * t⁻¹ = x⁻¹ := by
  obtain ⟨t, htC, ht⟩ := exists_orderOf_eq_two_mem_centralizer hset
  have hsyl := card_sylow_eq_two_of_standard_of_center_eq_bot hset hZ hI
  exact ⟨t, ht, htC, hsyl,
    inf_centralizer_eq_zpowers_of_standard_of_center_eq_bot hset hZ hI htC ht,
    centralizer_le_normalizer_of_standard hset.standard htC ht,
    fun u huC hu => exists_odd_conj_eq_of_orderOf_eq_two hset hsyl htC ht huC hu,
    (conj_eq_inv_of_odd_of_standard hset hsyl htC ht).1⟩


theorem exists_conj_mem_normalizer_not_mem_centralizer (hset : StandardSetting G L) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) :
    ∃ g : G, g⁻¹ * t * g ≠ t ∧ (g⁻¹ * t * g) * t = t * (g⁻¹ * t * g) ∧
      g⁻¹ * t * g ∈ normalizer (L : Set G) ∧ g⁻¹ * t * g ∉ centralizer (L : Set G) := by
  have := hset.simple
  obtain ⟨g, hne, hc⟩ := exists_conj_ne_commute_of_isSimpleGroup hset.nonab ht
  have hmem : g⁻¹ * t * g ∈ centralizer ({t} : Set G) := mem_centralizer_singleton_iff.2 hc
  refine ⟨g, hne, hc, centralizer_le_normalizer_of_standard hset.standard htC ht hmem,
    fun hC => ?_⟩
  have hz : g⁻¹ * t * g ∈ zpowers t := hK ▸ mem_inf.2 ⟨hC, hmem⟩
  rcases eq_one_or_eq_of_mem_zpowers ht hz with h1 | h1
  · have h1' : t = 1 := by
      calc t = g * (g⁻¹ * t * g) * g⁻¹ := by group
        _ = 1 := by rw [h1]; group
    rw [h1', orderOf_one] at ht
    exact absurd ht (by decide)
  · exact hne h1

omit [Finite G] in
theorem eq_or_eq_mul_of_conj_eq {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2)
    (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {x l : G}
    (hx : x ∈ centralizer ({t} : Set G)) (hl : l ∈ L)
    (hxl : ∀ y ∈ L, x * y * x⁻¹ = l * y * l⁻¹) : x = l ∨ x = l * t := by
  have hlC : l⁻¹ * x ∈ centralizer (L : Set G) := by
    rw [mem_centralizer_iff]
    intro y hy
    have h := hxl y hy
    calc y * (l⁻¹ * x) = l⁻¹ * (l * y * l⁻¹) * x := by group
      _ = l⁻¹ * (x * y * x⁻¹) * x := by rw [h]
      _ = l⁻¹ * x * y := by group
  have hlt : l ∈ centralizer ({t} : Set G) :=
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 htC l hl)
  have hz : l⁻¹ * x ∈ zpowers t :=
    hK ▸ mem_inf.2 ⟨hlC, mul_mem (inv_mem hlt) hx⟩
  rcases eq_one_or_eq_of_mem_zpowers ht hz with h1 | h1
  · left
    calc x = l * (l⁻¹ * x) := by group
      _ = l := by rw [h1, mul_one]
  · right
    calc x = l * (l⁻¹ * x) := by group
      _ = l * t := by rw [h1]

omit [Finite G] in
theorem mem_sup_zpowers_of_conj_eq {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2)
    (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {x l : G}
    (hx : x ∈ centralizer ({t} : Set G)) (hl : l ∈ L)
    (hxl : ∀ y ∈ L, x * y * x⁻¹ = l * y * l⁻¹) : x ∈ L ⊔ zpowers t := by
  rcases eq_or_eq_mul_of_conj_eq htC ht hK hx hl hxl with rfl | rfl
  · exact mem_sup_left hl
  · exact mul_mem (mem_sup_left hl) (mem_sup_right (mem_zpowers t))


end Standard

end CFSG.SeitzReduction.F4Pilot
