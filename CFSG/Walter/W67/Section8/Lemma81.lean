module

public import CFSG.Walter.W67.Lemma26i

public section

namespace CFSG.Walter.W67

open scoped MatrixGroups

namespace Lemma81

variable {G : Type} [Group G]

theorem index_ne_two_of_perfect (hperf : commutator G = ⊤) :
    ∀ N : Subgroup G, N.Normal → N.index ≠ 2 := by
  intro N hN h2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsCyclic (G ⧸ N) :=
    isCyclic_of_prime_card (p := 2) (by rw [← Subgroup.index_eq_card, h2])
  have h1 := Abelianization.commutator_subset_ker (QuotientGroup.mk' N)
  rw [QuotientGroup.ker_mk', hperf, top_le_iff] at h1
  rw [h1, Subgroup.index_top] at h2
  omega

theorem mem_oddPart_of_dihedral {Y : Subgroup G} {n : ℕ} (hn : n % 4 = 2)
    (e : Y ≃* DihedralGroup n) {y : G} (hy : y ∈ Y) (hodd : Odd (orderOf y)) :
    y ∈ oddPart Y := by
  have : NeZero n := ⟨by omega⟩
  set R : Subgroup (DihedralGroup n) := Subgroup.zpowers (DihedralGroup.r (2 : ZMod n)) with hR
  have hRn : R.Normal := by
    refine ⟨fun x hx g => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rcases g with i | i
    · rw [show DihedralGroup.r i * DihedralGroup.r 2 ^ k * (DihedralGroup.r i)⁻¹ =
        DihedralGroup.r 2 ^ k by
          rw [(Commute.zpow_right (show Commute (DihedralGroup.r i) (DihedralGroup.r 2) from
            by simp [Commute, SemiconjBy, add_comm]) k).eq, mul_inv_cancel_right]]
      exact Subgroup.zpow_mem_zpowers _ k
    · have hconj : DihedralGroup.sr i * DihedralGroup.r 2 * (DihedralGroup.sr i)⁻¹ =
          (DihedralGroup.r 2)⁻¹ := by
        simp [DihedralGroup.inv_sr]
      have : DihedralGroup.sr i * DihedralGroup.r 2 ^ k * (DihedralGroup.sr i)⁻¹ =
          ((DihedralGroup.r 2)⁻¹) ^ k := by
        rw [← hconj, conj_zpow]
      rw [this, inv_zpow']
      exact Subgroup.zpow_mem_zpowers _ (-k)
  have hRcard : Nat.Coprime 2 (Nat.card R) := by
    rw [Nat.card_zpowers, DihedralGroup.orderOf_r]
    have hval : Nat.gcd n (2 : ZMod n).val = 2 := by
      rcases Nat.lt_or_ge n 3 with h3 | h3
      · interval_cases n
        · omega
        · omega
        · rfl
      · have : (2 : ZMod n).val = 2 := by
          rw [show (2 : ZMod n) = ((2 : ℕ) : ZMod n) by norm_cast, ZMod.val_natCast]
          exact Nat.mod_eq_of_lt (by omega)
        rw [this]
        exact Nat.gcd_eq_right (Nat.dvd_of_mod_eq_zero (by omega))
    rw [hval]
    refine Nat.coprime_two_left.mpr (Nat.odd_iff.mpr ?_)
    have h' : n / 2 % 2 = 1 := by omega
    exact h'
  set N : Subgroup Y := R.comap e.toMonoidHom with hN
  have hNn : N.Normal := hRn.comap _
  have hNcard : Nat.Coprime 2 (Nat.card N) := by
    have : Nat.card N = Nat.card R := by
      rw [hN, ← Subgroup.card_map_of_injective (f := e.toMonoidHom) (by exact e.injective),
        Subgroup.map_comap_eq_self_of_surjective (f := e.toMonoidHom) (by exact e.surjective)]
    rwa [this]
  have hle : N ≤ CFSG.pPrimeCore 2 Y := CFSG.le_pPrimeCore_of_normal_coprime hNn hNcard
  have hmem : (⟨y, hy⟩ : Y) ∈ N := by
    change e ⟨y, hy⟩ ∈ R
    have hodd' : Odd (orderOf (e ⟨y, hy⟩)) := by
      rwa [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
    generalize e ⟨y, hy⟩ = x at hodd'
    rcases x with i | i
    · rw [DihedralGroup.orderOf_r] at hodd'
      have h2 : 2 ∣ i.val := by
        have hdi := Nat.gcd_dvd_right n i.val
        have hk : Nat.gcd n i.val * (n / Nat.gcd n i.val) = n :=
          Nat.mul_div_cancel' (Nat.gcd_dvd_left n i.val)
        have hev : Even (Nat.gcd n i.val) := by
          by_contra hno
          rw [Nat.not_even_iff_odd] at hno
          have : Odd n := hk ▸ hno.mul hodd'
          rw [Nat.odd_iff] at this
          omega
        exact (even_iff_two_dvd.mp hev).trans hdi
      obtain ⟨k, hk⟩ := h2
      have : DihedralGroup.r i = DihedralGroup.r (2 : ZMod n) ^ k := by
        have h1 : DihedralGroup.r i = (DihedralGroup.r 1 : DihedralGroup n) ^ i.val := by
          rw [DihedralGroup.r_one_pow, ZMod.natCast_zmod_val]
        have h2 : DihedralGroup.r (2 : ZMod n) = (DihedralGroup.r 1 : DihedralGroup n) ^ 2 := by
          rw [DihedralGroup.r_one_pow]
          norm_num
        rw [h1, h2, ← pow_mul, hk]
      rw [this]
      exact Subgroup.npow_mem_zpowers _ k
    · rw [DihedralGroup.orderOf_sr] at hodd'
      exact absurd hodd' (by decide)
  exact ⟨⟨y, hy⟩, hle hmem, rfl⟩

section PSL

variable {p f : ℕ} [Fact p.Prime] {K : Subgroup G}

theorem inf_centralizer_eq_map (e : K ≃* PSL(2, GaloisField p f)) {t : G}
    {t' : PSL(2, GaloisField p f)} (ht' : psl2Emb e t' = t) :
    K ⊓ Subgroup.centralizer ({t} : Set G) =
      (Subgroup.centralizer ({t'} : Set PSL(2, GaloisField p f))).map (psl2Emb e) := by
  ext x
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_map]
  constructor
  · rintro ⟨hxK, hxt⟩
    obtain ⟨y, rfl⟩ := PSL2Sub.exists_emb_eq e hxK
    refine ⟨y, PSL2Sub.emb_injective e ?_, rfl⟩
    rw [map_mul, map_mul, ht']
    exact hxt
  · rintro ⟨y, hy, rfl⟩
    refine ⟨PSL2Sub.emb_mem e y, ?_⟩
    rw [← ht', ← map_mul, ← map_mul, hy]

theorem mem_oddPart_inf_centralizer (e : K ≃* PSL(2, GaloisField p f)) (hp : Odd p)
    (hf : 0 < f) (hq : p ^ f % 8 = 3) {t : G} (htK : t ∈ K) (ht : orderOf t = 2) {y : G}
    (hy : y ∈ K ⊓ Subgroup.centralizer ({t} : Set G)) (hodd : Odd (orderOf y)) :
    y ∈ oddPart (K ⊓ Subgroup.centralizer ({t} : Set G)) := by
  obtain ⟨t', ht'⟩ := PSL2Sub.exists_emb_eq e htK
  have ht'2 : orderOf t' = 2 := by
    rw [← orderOf_injective (psl2Emb e) (PSL2Sub.emb_injective e) t', ht', ht]
  obtain ⟨-, ⟨d⟩⟩ := (psl2_odd_centralizer_involution hp hf ht'2).2 (by omega)
  let iso1 : (K ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) ≃*
      Subgroup.centralizer ({t'} : Set PSL(2, GaloisField p f)) :=
    (MulEquiv.subgroupCongr (inf_centralizer_eq_map e ht')).trans
      (Subgroup.equivMapOfInjective _ _ (PSL2Sub.emb_injective e)).symm
  exact mem_oddPart_of_dihedral (n := (p ^ f + 1) / 2) (by omega) (iso1.trans d) hy hodd


end PSL

end Lemma81


namespace Lemma81

variable {G : Type} [Group G] [Finite G]

theorem three_pow_mod_eight_of_odd {f : ℕ} (hf : Odd f) : 3 ^ f % 8 = 3 := by
  obtain ⟨k, rfl⟩ := hf
  rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
  norm_num


theorem exists_involution_T {h : Hyp G} (fr : Frame h) :
    ∃ T₂ ∈ fr.T, orderOf T₂ = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := fr.T) 2
    (by rw [fr.card_T]; norm_num)
  exact ⟨t, t.2, by rw [← ht, Subgroup.orderOf_coe]⟩

end Lemma81


end CFSG.Walter.W67
