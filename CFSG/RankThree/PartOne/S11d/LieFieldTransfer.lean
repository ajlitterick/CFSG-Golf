module

public import CFSG.RankThree.PartOne.S11d.LieComponentTransfer
public import CFSG.RankThree.PartOne.S11d.FieldFFTwo

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG
open scoped commutatorElement

variable {G : Type} [Group G]

theorem not_le_center_of_isQuasisimple' {X : Type*} [Group X] {Q : Subgroup X}
    (hQ : CFSG.IsQuasisimple ↥Q) : ¬ Q ≤ Subgroup.center X := by
  intro hle
  obtain ⟨-, -, a, b, hab⟩ := hQ
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  apply hab
  have h : a * b = b * a := Subtype.ext (Subgroup.mem_center_iff.mp (hle a.2) b).symm
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h]

theorem isComponentOf_map_centerQuotient {p : ℕ} (hp : p.Prime) {J : Subgroup G}
    (hZ : ¬ p ∣ Nat.card (Subgroup.center ↥J)) {d : G} (hdJ : d ∈ J) (hdp : d ^ p = 1)
    {D : Subgroup G} (hD : IsComponentOf (J ⊓ Subgroup.centralizer ({d} : Set G)) D) :
    IsComponentOf (Subgroup.centralizer ({((⟨d, hdJ⟩ : ↥J) : ↥J ⧸ Subgroup.center ↥J)} :
        Set (↥J ⧸ Subgroup.center ↥J)))
      ((D.subgroupOf J).map (QuotientGroup.mk' (Subgroup.center ↥J))) := by
  set π : ↥J →* ↥J ⧸ Subgroup.center ↥J := QuotientGroup.mk' (Subgroup.center ↥J) with hπ
  set dJ : ↥J := ⟨d, hdJ⟩ with hdJdef
  set X : Subgroup G := J ⊓ Subgroup.centralizer ({d} : Set G) with hX
  have hdJp : dJ ^ p = 1 := Subtype.ext hdp
  have hker : π.ker ≤ Subgroup.center ↥J := by rw [hπ, QuotientGroup.ker_mk']
  set N : Subgroup ↥J := Subgroup.centralizer ({dJ} : Set ↥J) with hN
  have hCT : Subgroup.centralizer
      ({(dJ : ↥J ⧸ Subgroup.center ↥J)} : Set (↥J ⧸ Subgroup.center ↥J)) = N.map π := by
    ext t
    constructor
    · intro ht
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥J) t
      exact ⟨g, mem_centralizer_of_map_mem_centralizer π hker hp hZ hdJp ht, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      have := Subgroup.mem_centralizer_singleton_iff.mp hg
      change π g * π dJ = π dJ * π g
      rw [← map_mul, ← map_mul, this]
  have hDX : D ≤ X := hD.1
  have hDJ : D ≤ J := hDX.trans inf_le_left
  set D' : Subgroup ↥J := D.subgroupOf J with hD'
  have hD'N : D' ≤ N := by
    intro g hg
    have hgD : (g : G) ∈ D := Subgroup.mem_subgroupOf.mp hg
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hDX hgD).2
    exact Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext h1)
  have hD'q : CFSG.IsQuasisimple ↥D' :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hDJ).symm hD.2.1
  have hD'nc : ¬ D' ≤ π.ker := fun hle =>
    not_le_center_of_isQuasisimple' hD'q (hle.trans hker)
  refine ⟨?_, ?_, ?_⟩
  · rw [hCT]
    exact Subgroup.map_mono hD'N
  · exact CFSG.LocalCores.isQuasisimple_map hD'q π hD'nc
  ·
    let ψ : ↥X →* ↥(Subgroup.centralizer
        ({(dJ : ↥J ⧸ Subgroup.center ↥J)} : Set (↥J ⧸ Subgroup.center ↥J))) :=
      (π.comp (Subgroup.inclusion (inf_le_left : X ≤ J))).codRestrict _ (fun x => by
        rw [hCT]
        exact ⟨Subgroup.inclusion (inf_le_left : X ≤ J) x,
          Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext
            (Subgroup.mem_centralizer_singleton_iff.mp x.2.2)), rfl⟩)
    have hψ : Function.Surjective ψ := by
      rintro ⟨t, ht⟩
      rw [hCT] at ht
      obtain ⟨g, hg, rfl⟩ := ht
      have hgX : (g : G) ∈ X := ⟨g.2, Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hg))⟩
      exact ⟨⟨g, hgX⟩, rfl⟩
    have hmap : ((D.subgroupOf J).map π).subgroupOf (Subgroup.centralizer
        ({(dJ : ↥J ⧸ Subgroup.center ↥J)} : Set (↥J ⧸ Subgroup.center ↥J))) =
          (D.subgroupOf X).map ψ := by
      ext ⟨t, ht⟩
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map]
      constructor
      · rintro ⟨g, hg, rfl⟩
        have hgN : g ∈ N := hD'N hg
        have hgD : (g : G) ∈ D := Subgroup.mem_subgroupOf.mp hg
        have hgX : (g : G) ∈ X := hDX hgD
        exact ⟨⟨g, hgX⟩, hgD, Subtype.ext rfl⟩
      · rintro ⟨x, hx, hxt⟩
        refine ⟨Subgroup.inclusion (inf_le_left : X ≤ J) x, ?_, ?_⟩
        · exact hx
        · exact congrArg Subtype.val hxt
    rw [hmap]
    exact hD.2.2.map hψ


section Reduction

open CFSG.Blueprint (LieModel)
open CFSG.Assembly.LowTwoRank (StatedLieTag)
open CFSG.RankThree.PartOne.Sec66T
open CFSG.RankThree.PartOne.FieldFix
open CFSG.LieType.CurtisTits (lieModel_of_mulEquiv)


theorem exists_mul_of_mem_sup_centralizer_self (D : Subgroup G) {z : G}
    (hz : z ∈ D ⊔ Subgroup.centralizer (D : Set G)) :
    ∃ e ∈ D, ∃ c ∈ Subgroup.centralizer (D : Set G), z = e * c := by
  have hDN : D ≤ Subgroup.normalizer ((Subgroup.centralizer (D : Set G) : Subgroup G) : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have h0 : g * x = x * g := (Subgroup.mem_centralizer_iff.mp hx) g hg
      have h1 : g * x * g⁻¹ = x := by rw [h0, mul_assoc, mul_inv_cancel, mul_one]
      rw [h1]
      exact hx
    · intro hy
      rw [Subgroup.mem_centralizer_iff] at hy ⊢
      intro h₀ hh₀
      have h2 := hy (g * h₀ * g⁻¹) (D.mul_mem (D.mul_mem hg hh₀) (D.inv_mem hg))
      have h3 : g * (h₀ * x) * g⁻¹ = g * (x * h₀) * g⁻¹ := by
        calc g * (h₀ * x) * g⁻¹ = (g * h₀ * g⁻¹) * (g * x * g⁻¹) := by group
          _ = (g * x * g⁻¹) * (g * h₀ * g⁻¹) := h2
          _ = g * (x * h₀) * g⁻¹ := by group
      exact mul_left_cancel (mul_right_cancel h3)
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hDN] at hz
  obtain ⟨e, he, c, hc, rfl⟩ := hz
  exact ⟨e, he, c, hc, rfl⟩

theorem centerQuotientConj_mk_apply {J : Subgroup G} {u : G}
    (hu : u ∈ Subgroup.normalizer (J : Set G)) (g : ↥J) :
    centerQuotientConj J ⟨u, hu⟩ (g : ↥J ⧸ Subgroup.center ↥J) =
      ((⟨u * (g : G) * u⁻¹, (Subgroup.mem_normalizer_iff.mp hu (g : G)).mp g.2⟩ : ↥J) :
        ↥J ⧸ Subgroup.center ↥J) := rfl

theorem nonempty_centerQuotientEquiv_of_surjective {P Q : Type*} [Group P] [Group Q]
    (hP : Group.IsPerfect P) (f : P →* Q) (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center P) :
    Nonempty (P ⧸ Subgroup.center P ≃* Q ⧸ Subgroup.center Q) := by
  have hc : Subgroup.center P = ((QuotientGroup.mk' (Subgroup.center Q)).comp f).ker := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    exact (CFSG.LocalCores.comap_center_eq_of_perfect hP f hf hker).symm
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hc).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ ((QuotientGroup.mk'_surjective _).comp hf))⟩

variable [Finite G]

theorem exists_two_element_lift {p : ℕ} (hp : p.Prime) {J : Subgroup G}
    (hZ : ¬ p ∣ Nat.card (Subgroup.center ↥J)) (hZ2 : ¬ 2 ∣ Nat.card (Subgroup.center ↥J))
    {u : G} (hu : u ∈ Subgroup.normalizer (J : Set G)) (hup : u ^ p = 1) {D : Subgroup G}
    {t : ↥J ⧸ Subgroup.center ↥J}
    (ht : t ∈ (D.subgroupOf J).map (QuotientGroup.mk' (Subgroup.center ↥J)))
    (hαt : centerQuotientConj J ⟨u, hu⟩ t = t) (hord : ∃ k : ℕ, orderOf t = 2 ^ k) :
    ∃ g : G, g ∈ D ∧ u * g * u⁻¹ = g ∧ (∃ k : ℕ, orderOf g = 2 ^ k) ∧
      ∃ hg : g ∈ J, ((⟨g, hg⟩ : ↥J) : ↥J ⧸ Subgroup.center ↥J) = t := by
  obtain ⟨θ, hθs, -, hθ⟩ := exists_fixed_hom hp hZ hu hup
  obtain ⟨x, hx⟩ := hθs ⟨t, hαt⟩
  let ρ : ↥(J ⊓ Subgroup.centralizer ({u} : Set G)) →* ↥J ⧸ Subgroup.center ↥J :=
    (QuotientGroup.mk' (Subgroup.center ↥J)).comp
      (Subgroup.inclusion (inf_le_left : J ⊓ Subgroup.centralizer ({u} : Set G) ≤ J))
  have hρx : ρ x = t := by
    have h1 := hθ x
    rw [hx] at h1
    exact h1.symm
  obtain ⟨k, hk⟩ := hord
  set a := (orderOf x).factorization 2 with ha
  set o := orderOf x / 2 ^ a with ho
  have hord0 : orderOf x ≠ 0 := (orderOf_pos x).ne'
  have hno : 2 ^ a * o = orderOf x := Nat.ordProj_mul_ordCompl_eq_self (orderOf x) 2
  have hc2o : Nat.Coprime 2 o := Nat.coprime_ordCompl Nat.prime_two hord0
  have hcop : Nat.Coprime (2 ^ a) o := hc2o.pow_left a
  obtain ⟨e, he1, he0⟩ := Nat.chineseRemainder hcop 1 0
  have hoe : o ∣ e := (Nat.modEq_zero_iff_dvd).1 he0
  have hxe : (x ^ e) ^ (2 ^ a) = 1 := by
    obtain ⟨c, hc⟩ := hoe
    rw [← pow_mul, hc, show o * c * 2 ^ a = orderOf x * c by rw [← hno]; ring, pow_mul,
      pow_orderOf_eq_one, one_pow]
  have hkdvd : 2 ^ k ∣ orderOf x := by
    rw [← hk, ← hρx]
    exact orderOf_map_dvd ρ x
  have hka : 2 ^ k ∣ 2 ^ a := (hc2o.pow_left k).dvd_of_dvd_mul_right (hno ▸ hkdvd)
  have hρxe : ρ (x ^ e) = t := by
    rw [map_pow, hρx]
    have hmod : e ≡ 1 [MOD orderOf t] := by
      rw [hk]
      exact Nat.ModEq.of_dvd hka he1
    calc t ^ e = t ^ 1 := pow_eq_pow_iff_modEq.mpr hmod
      _ = t := pow_one t
  set g : G := (((x ^ e : ↥(J ⊓ Subgroup.centralizer ({u} : Set G))) : G)) with hg
  have hgX : g ∈ J ⊓ Subgroup.centralizer ({u} : Set G) := (x ^ e).2
  have hgJ : g ∈ J := hgX.1
  have hgu : u * g * u⁻¹ = g := by
    have h1 : g * u = u * g := Subgroup.mem_centralizer_singleton_iff.mp hgX.2
    rw [← h1, mul_assoc, mul_inv_cancel, mul_one]
  have hgord : ∃ b : ℕ, orderOf g = 2 ^ b := by
    have h1 : orderOf g ∣ 2 ^ a := by
      rw [hg, Subgroup.orderOf_coe]
      exact orderOf_dvd_of_pow_eq_one hxe
    obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
    exact ⟨b, hb⟩
  have hgt : ((⟨g, hgJ⟩ : ↥J) : ↥J ⧸ Subgroup.center ↥J) = t := hρxe
  obtain ⟨e', he', hπe'⟩ := ht
  set gJ : ↥J := ⟨g, hgJ⟩ with hgJdef
  have hz : gJ⁻¹ * e' ∈ Subgroup.center ↥J := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    have : (e' : ↥J ⧸ Subgroup.center ↥J) = t := hπe'
    rw [this, ← hgt, inv_mul_cancel]
  set z : ↥J := gJ⁻¹ * e' with hzdef
  have hee : e' = gJ * z := by rw [hzdef, mul_inv_cancel_left]
  obtain ⟨b, hb⟩ := hgord
  have hzord : orderOf z ∣ Nat.card (Subgroup.center ↥J) := by
    have := orderOf_dvd_natCard (⟨z, hz⟩ : Subgroup.center ↥J)
    rwa [Subgroup.orderOf_mk] at this
  have hzcomm : Commute gJ z := Subgroup.mem_center_iff.mp hz gJ
  have hZodd : Odd (Nat.card (Subgroup.center ↥J)) := Nat.odd_iff.mpr (by omega)
  have hrodd : Odd (orderOf z) := Odd.of_dvd_nat hZodd hzord
  have hgJord : orderOf gJ = 2 ^ b := by rw [hgJdef, Subgroup.orderOf_mk]; exact hb
  have hr2 : Nat.Coprime (orderOf z) (orderOf gJ) := by
    rw [hgJord]
    exact (Odd.coprime_two_right hrodd).pow_right b
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hr2
  have hzr : z ^ orderOf z = 1 := pow_orderOf_eq_one z
  have hmem : gJ ∈ D.subgroupOf J := by
    have h1 : e' ^ orderOf z = gJ ^ orderOf z := by
      rw [hee, hzcomm.mul_pow, hzr, mul_one]
    rw [← hm, ← h1]
    exact (D.subgroupOf J).pow_mem ((D.subgroupOf J).pow_mem he' _) m
  exact ⟨g, Subgroup.mem_subgroupOf.mp hmem, hgu, ⟨b, hb⟩, hgJ, hgt⟩


end Reduction

end CFSG.RankThree.PartOne
