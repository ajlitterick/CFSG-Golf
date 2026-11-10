module

public import CFSG.Quasithin.Vol2.Ch11SecB21Odd
public import CFSG.Quasithin.Vol2.Ch11SecB21J
public import CFSG.Quasithin.Vol2.Ch11SecBDerived
public import CFSG.Quasithin.Vol2.Ch11SecBDerived35
public import CFSG.Quasithin.Vol2.Ch11SecBFacts35
public import CFSG.Quasithin.Vol2.Ch11SecAVi2
public import CFSG.Quasithin.Background.A4FourQuot
public import CFSG.Quasithin.Vol2.Ch3Sec1Thm318
public import CFSG.Quasithin.Background.C2Nine
public import CFSG.Quasithin.Background.BlueprintB2Bridge
public import CFSG.Quasithin.Vol2.Ch11SecBBasic

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin.Vol2.Ch11.SecA
open scoped Pointwise

section General

variable {G : Type} [Group G] [Finite G]

theorem oTwoUpper_eq_conjClosure {H K T : Subgroup G} (hK : ⁅K, K⁆ = K) (hT : IsPGroup 2 T)
    (hHK : H = K ⊔ T) : oTwoUpper H = conjClosure K H := by
  have hKH : K ≤ H := hHK ▸ le_sup_left
  apply le_antisymm
  · refine oTwoUpper_le_of_pow_mem ?_
    have hCH : conjClosure K H ≤ H := conjClosure_le fun h hh z hz =>
      H.mul_mem (H.mul_mem hh (hKH hz)) (H.inv_mem hh)
    have hsup : T ⊔ conjClosure K H = H :=
      le_antisymm (sup_le (hHK ▸ le_sup_right) hCH)
        (hHK.le.trans (sup_le ((le_conjClosure K H).trans le_sup_right) le_sup_left))
    exact B6.isTwoQuotient_of_sup_eq hT (le_normalizer_conjClosure K H) hsup
  · refine conjClosure_le fun h hh z hz => ?_
    have hzO : z ∈ oTwoUpper H := perfect_le_oTwoUpper hKH (Subgroup.isPerfect_iff.2 hK) hz
    exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_oTwoUpper H hh) z).mp hzO

omit [Finite G] in
theorem commutator_quotient_eq_top {K : Subgroup G} (hK : ⁅K, K⁆ = K) (N : Subgroup ↥K)
    [N.Normal] : commutator (↥K ⧸ N) = ⊤ := by
  have hXp : commutator ↥K = ⊤ := Group.isPerfect_def.1 (Subgroup.isPerfect_iff.2 hK)
  have hsurj := QuotientGroup.mk'_surjective N
  calc commutator (↥K ⧸ N) = ⁅(⊤ : Subgroup (↥K ⧸ N)), ⊤⁆ := commutator_def _
    _ = ⁅(⊤ : Subgroup ↥K).map (QuotientGroup.mk' N), (⊤ : Subgroup ↥K).map
          (QuotientGroup.mk' N)⁆ := by
        rw [Subgroup.map_top_of_surjective _ hsurj]
    _ = Subgroup.map (QuotientGroup.mk' N) ⁅(⊤ : Subgroup ↥K), ⊤⁆ :=
        (Subgroup.map_commutator _ _ _).symm
    _ = ⊤ := by rw [← commutator_def, hXp, Subgroup.map_top_of_surjective _ hsurj]

omit [Finite G] in
theorem even_of_three_dvd {n : ℕ} (h : 3 ∣ 2 ^ n - 1) : Even n := by
  rcases Nat.even_or_odd n with he | ⟨m, rfl⟩
  · exact he
  · exfalso
    have h1 : 2 ^ (2 * m + 1) % 3 = 2 := by
      rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
      norm_num
    have h2 : 1 ≤ 2 ^ (2 * m + 1) := Nat.one_le_two_pow
    generalize 2 ^ (2 * m + 1) = x at h h1 h2
    omega

end General

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem eq_commutator_thompsonJ_of_moves (hC58 : TheoremC58) (h317 : AS317Sylow)
    (h3228 : Ch10.TmpL6_3_2_2_eight) (hFC : FactCentralizerTwo) (h331 : Stmt3_3_1)
    (h1102 : Stmt11_0_2) (hyp : Hyp11 G T L I n) {H : Subgroup G}
    (hH : IsHStar T (Subgroup.normalizer (L : Set G)) H)
    (hZH : ⁅quasithinOmegaOneCenter T, H⁆ ≠ ⊥) : L = ⁅L, thompsonJ T⁆ := by
  refine eq_commutator_thompsonJ hFC h1102 hyp fun hJ => hZH ?_
  obtain ⟨hVLT, hVred, hcent⟩ := h3228 G T L I hyp.fsu
  rw [fsuL0_eq hyp] at hVLT hVred hcent
  have h318 : Hyp318 T (Subgroup.normalizer (L : Set G)) L (fsuV T I) :=
    { inM := ⟨isMaxTwoLocal_M h331 hyp, hyp.normal⟩
      nonempty := ⟨H, hH⟩
      perfect := (C2Nine.oTwoUpper_eq_of_perfect hyp.fsu.faithful.1.2.1.2.1).symm
      le_M := Subgroup.le_normalizer
      normal := le_rfl
      unique := isUniqueM_LT h331 hyp
      reduced := isTwoReducedIn_iff_isPrimeReduced_subgroupOf.2 ⟨hVLT, hVred⟩
      centralizer := hcent }
  rcases theorem318_three hC58 h317 hyp.fsu.simple hyp.fsu.nonabelian hyp.fsu.qtke
      hyp.fsu.sylow h318 with h | ⟨-, hZ, -⟩
  · exact absurd hJ h.1
  · rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact (hZ H hH).trans inf_le_right

theorem le_of_dvd_two_pow_sub_one (h1102 : Stmt11_0_2) (h1104 : Stmt11_0_4)
    (hyp : Hyp11 G T L I n) (hLJ : L = ⁅L, thompsonJ T⁆) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpd : p ∣ 2 ^ n - 1) {Dp : Subgroup G} (hDM : Dp ≤ Subgroup.normalizer (L : Set G))
    (hDp : ∀ x ∈ Dp, x ^ p = 1) : Dp ≤ L := by
  have : Fact p.Prime := ⟨hp⟩
  have h04 := h1104 G T L I n hyp
  have hpd2 : p ∣ 2 ^ (2 * n) - 1 := by
    refine hpd.trans ⟨2 ^ n + 1, ?_⟩
    have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have h3 : 1 ≤ 2 ^ n * 2 ^ n := Nat.one_le_iff_ne_zero.mpr (by positivity)
    rw [two_mul, pow_add]
    zify [h1, h3]
    ring
  intro x hx
  by_cases hx1 : x = 1
  · rw [hx1]; exact L.one_mem
  have hord : orderOf x = p := orderOf_eq_prime (hDp x hx) hx1
  have hres : ∀ q : ℕ, q.Prime → oPrimeResidualOf q (Subgroup.normalizer (L : Set G)) = L →
      orderOf x = q → x ∈ L := fun q _ hq hxq => by
    rw [← hq]
    exact Subgroup.subset_closure ⟨hDM hx, 1, by rw [hxq, pow_one]⟩
  rcases kind_cases h1102 hyp with hk | hk | hk
  · by_cases hp3 : p = 3
    · exact h04.2 hk (even_of_three_dvd (hp3 ▸ hpd)) x (hDM hx) (hp3 ▸ hord)
        (Or.inr (Or.inl hLJ))
    · have h3 : 3 < p := by
        have := hp.two_le
        omega
      exact hres p hp (h04.1 p hp (Or.inr ⟨hk, hpd, h3⟩)) hord
  · exact hres p hp (h04.1 p hp (Or.inl ⟨Or.inl hk, hpd2⟩)) hord
  · exact hres p hp (h04.1 p hp (Or.inl ⟨Or.inr hk, hpd2⟩)) hord


end CFSG.Quasithin.Vol2.Ch11.SecB
