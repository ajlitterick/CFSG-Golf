module

public import CFSG.LocalAnalysis.ComponentInitial.BasicFacts
public import CFSG.LocalAnalysis.SectionRank.SQT

public section

namespace CFSG.ComponentClassification.UnbalancedGS

namespace RankOneCenter

open Subgroup

variable {p : ℕ} [hp : Fact p.Prime]

theorem le_pRank_of_subgroup {K : Type*} [Group K] [Finite K] {A : Subgroup K}
    (hA : IsElementaryAbelian p A) {r : ℕ} (hr : Nat.card A = p ^ r) : r ≤ pRank p K := by
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
  exact CFSG.SectionRank.le_pRank hp.out.one_lt le_top
    ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p A).mp hA) hr


theorem card_sup_mul_card_inf_of_commute {H : Type*} [Group H] [Finite H] (L R : Subgroup H)
    (hc : ∀ x ∈ L, ∀ y ∈ R, x * y = y * x) :
    Nat.card (L ⊔ R : Subgroup H) * Nat.card (L ⊓ R : Subgroup H) = Nat.card L * Nat.card R := by
  let μ : L × R →* H := MonoidHom.noncommCoprod L.subtype R.subtype fun x y => hc x x.2 y y.2
  have hμ : ∀ x : L × R, μ x = (x.1 : H) * x.2 := fun _ => rfl
  have hrange : μ.range = L ⊔ R := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      rw [hμ]
      exact mul_mem (Subgroup.mem_sup_left x.1.2) (Subgroup.mem_sup_right x.2.2)
    · refine sup_le (fun l hl => ⟨(⟨l, hl⟩, 1), by rw [hμ]; simp⟩)
        (fun r hr => ⟨(1, ⟨r, hr⟩), by rw [hμ]; simp⟩)
  have hker : Nat.card μ.ker = Nat.card (L ⊓ R : Subgroup H) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨(x.1.1 : H), x.1.1.2, ?_⟩
        invFun := fun z => ⟨(⟨z, z.2.1⟩, ⟨(z : H)⁻¹, inv_mem z.2.2⟩), ?_⟩
        left_inv := fun x => ?_
        right_inv := fun z => rfl }
    · have h := x.2
      rw [MonoidHom.mem_ker, hμ, mul_eq_one_iff_eq_inv] at h
      rw [h]
      exact R.inv_mem x.1.2.2
    · rw [MonoidHom.mem_ker, hμ]
      exact mul_inv_cancel _
    · apply Subtype.ext
      have h := x.2
      rw [MonoidHom.mem_ker, hμ, mul_eq_one_iff_inv_eq] at h
      exact Prod.ext rfl (Subtype.ext h)
  have := Subgroup.card_ker_mul_card_range μ
  rw [hrange, hker, Nat.card_prod] at this
  rw [mul_comm]
  exact this

theorem pair_isElementaryAbelian_card {H : Type*} [Group H] [Finite H] {t x : H}
    (ht : orderOf t = p) (hx : orderOf x = p) (hcomm : t * x = x * t) (hxt : x ∉ zpowers t) :
    IsElementaryAbelian p (zpowers t ⊔ zpowers x : Subgroup H) ∧
      Nat.card (zpowers t ⊔ zpowers x : Subgroup H) = p ^ 2 := by
  have : IsElementaryAbelian p (zpowers t) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one (ht ▸ pow_orderOf_eq_one t)
  have : IsElementaryAbelian p (zpowers x) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one (hx ▸ pow_orderOf_eq_one x)
  have hc : ∀ a ∈ zpowers t, ∀ b ∈ zpowers x, a * b = b * a := by
    intro a ha b hb
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hb
    exact (Commute.zpow_zpow hcomm i j).eq
  refine ⟨IsElementaryAbelian.sup_of_le_centralizer ?_, ?_⟩
  · rw [zpowers_le, mem_centralizer_iff]
    intro a ha
    exact hc a ha x (mem_zpowers x)
  · have hinf : (zpowers t ⊓ zpowers x : Subgroup H) = ⊥ := by
      have hdvd : Nat.card (zpowers t ⊓ zpowers x : Subgroup H) ∣ p := by
        rw [← hx, ← Nat.card_zpowers]
        exact card_dvd_of_le inf_le_right
      rcases (Nat.dvd_prime hp.out).mp hdvd with h | h
      · exact eq_bot_of_card_eq _ h
      · exfalso
        have heq : (zpowers t ⊓ zpowers x : Subgroup H) = zpowers x :=
          eq_of_le_of_card_ge inf_le_right (by rw [h, Nat.card_zpowers, hx])
        have hmem : x ∈ (zpowers t ⊓ zpowers x : Subgroup H) := by
          rw [heq]
          exact mem_zpowers x
        exact hxt (mem_inf.mp hmem).1
    have h := card_sup_mul_card_inf_of_commute _ _ hc
    rw [hinf, card_bot, mul_one, Nat.card_zpowers, Nat.card_zpowers, ht, hx] at h
    rw [h, pow_two]

variable {G : Type*} [Group G]

theorem mem_map_center_iff {T : Subgroup G} {x : G} :
    x ∈ (center T).map T.subtype ↔ x ∈ T ∧ ∀ y ∈ T, y * x = x * y := by
  constructor
  · rintro ⟨x', hx', rfl⟩
    refine ⟨x'.2, fun y hy => ?_⟩
    exact congrArg Subtype.val (mem_center_iff.mp hx' ⟨y, hy⟩)
  · rintro ⟨hxT, hx⟩
    exact ⟨⟨x, hxT⟩, mem_center_iff.mpr fun y => Subtype.ext (hx y y.2), rfl⟩

variable [Finite G]

theorem mem_zpowers_of_pRank_center_le_one {T : Subgroup G} (hrank : pRank p (center T) ≤ 1)
    {t x : G} (ht : t ∈ (center T).map T.subtype) (hx : x ∈ (center T).map T.subtype)
    (hto : orderOf t = p) (hxo : orderOf x = p) : x ∈ zpowers t := by
  obtain ⟨t', ht'Z, rfl⟩ := mem_map.mp ht
  obtain ⟨x', hx'Z, rfl⟩ := mem_map.mp hx
  by_contra hxt
  let t'' : center T := ⟨t', ht'Z⟩
  let x'' : center T := ⟨x', hx'Z⟩
  have hto'' : orderOf t'' = p := by
    rw [← hto, Subgroup.coe_subtype, Subgroup.orderOf_coe, ← Subgroup.orderOf_coe t'']
  have hxo'' : orderOf x'' = p := by
    rw [← hxo, Subgroup.coe_subtype, Subgroup.orderOf_coe, ← Subgroup.orderOf_coe x'']
  have hcomm : t'' * x'' = x'' * t'' := Subtype.ext (mem_center_iff.mp hx'Z t')
  have hxt'' : x'' ∉ zpowers t'' := by
    rintro ⟨k, hk⟩
    apply hxt
    refine ⟨k, ?_⟩
    have := congrArg (fun z : center T => ((z : T) : G)) hk
    simpa [t'', x''] using this
  have h := pair_isElementaryAbelian_card hto'' hxo'' hcomm hxt''
  have := le_pRank_of_subgroup h.1 h.2
  omega

theorem commute_of_normalizes {T : Subgroup G} (hrank : pRank p (center T) ≤ 1) {t u : G}
    (ht : t ∈ (center T).map T.subtype) (hto : orderOf t = p)
    (hu : ∀ y ∈ T, u * y * u⁻¹ ∈ T) (hu' : ∀ y ∈ T, u⁻¹ * y * u ∈ T) {m : ℕ}
    (hum : u ^ (p ^ m) = 1) : u * t = t * u := by
  have htT := (mem_map_center_iff.mp ht)
  have hs : u * t * u⁻¹ ∈ (center T).map T.subtype := by
    refine mem_map_center_iff.mpr ⟨hu t htT.1, fun y hy => ?_⟩
    have hc := htT.2 _ (hu' y hy)
    calc y * (u * t * u⁻¹) = u * ((u⁻¹ * y * u) * t) * u⁻¹ := by group
      _ = u * (t * (u⁻¹ * y * u)) * u⁻¹ := by rw [hc]
      _ = u * t * u⁻¹ * y := by group
  have hso : orderOf (u * t * u⁻¹) = p := by
    rw [← hto]
    exact orderOf_injective (MulAut.conj u).toMonoidHom (MulAut.conj u).injective t
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp
    (mem_zpowers_of_pRank_center_le_one hrank ht hs hto hso)
  have hiter : ∀ n : ℕ, u ^ n * t * (u ^ n)⁻¹ = t ^ (k ^ n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hc : ∀ j : ℤ, u * t ^ j * u⁻¹ = (u * t * u⁻¹) ^ j := fun j => by
        simpa only [MulAut.conj_apply] using map_zpow (MulAut.conj u) t j
      calc u ^ (n + 1) * t * (u ^ (n + 1))⁻¹ = u * (u ^ n * t * (u ^ n)⁻¹) * u⁻¹ := by group
        _ = t ^ (k ^ (n + 1)) := by rw [ih, hc, ← hk, ← zpow_mul, pow_succ, mul_comm]
  have hfix := hiter (p ^ m)
  rw [hum, one_mul, inv_one, mul_one] at hfix
  have hmod : (k : ZMod p) = 1 := by
    have h1 : t ^ (k ^ p ^ m) = t ^ (1 : ℤ) := by rw [← hfix, zpow_one]
    rw [zpow_eq_zpow_iff_modEq, hto] at h1
    have h2 := (ZMod.intCast_eq_intCast_iff _ _ p).mpr h1
    push_cast at h2
    rwa [ZMod.pow_card_pow] at h2
  have hk1 : t ^ k = t := by
    conv_rhs => rw [← zpow_one t]
    rw [zpow_eq_zpow_iff_modEq, hto]
    exact (ZMod.intCast_eq_intCast_iff _ _ p).mp (by rw [hmod, Int.cast_one])
  rw [hk1] at hk
  calc u * t = u * t * u⁻¹ * u := by group
    _ = t * u := by rw [← hk]

end RankOneCenter

open RankOneCenter Subgroup


end CFSG.ComponentClassification.UnbalancedGS
