module

public import CFSG.Quasithin.Background.RonanF615
public import CFSG.Open.GeneralizedFittingSelfCentralizingMilestoneDefs
public import CFSG.LocalAnalysis.SectionRank.SubgroupRank
public import CFSG.LocalAnalysis.SectionRank.GroupRankTransport
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.LocalAnalysis.ComponentClassification.LocalComponents
public import CFSG.RankThree.PartTwo.Sec4.Item413Eigen

public section

namespace CFSG.Quasithin.RonanF615

open CFSG.Open


theorem three_ne_zero_of_card {K : Type} [Field K] [Finite K] {n : ℕ}
    (hcard : Nat.card K = (2 ^ n) ^ 2) : (3 : K) ≠ 0 := by
  intro h
  have : Fintype K := Fintype.ofFinite K
  have h3 : ((3 : ℕ) : K) = 0 := by exact_mod_cast h
  haveI : CharP K 3 := (CharP.charP_iff_prime_eq_zero Nat.prime_three).mpr h3
  obtain ⟨m, -, hm⟩ := FiniteField.card K 3
  rw [← Nat.card_eq_fintype_card, hcard] at hm
  have h3d : 3 ∣ (2 ^ n) ^ 2 := by
    rw [hm]
    exact dvd_pow_self 3 m.pos.ne'
  have := Nat.prime_three.dvd_of_dvd_pow (Nat.prime_three.dvd_of_dvd_pow h3d)
  omega

theorem pRank_three_le_two_of_statedSU {n : ℕ} {X : Type} [Group X] [Finite X]
    (h : ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = (2 ^ n) ^ 2 ∧
      Nonempty (X ≃* ↥(CFSG.Open.StatedSU 3 (2 ^ n) K))) : CFSG.pRank 3 X ≤ 2 := by
  obtain ⟨K, hK, hKf, hcard, ⟨e⟩⟩ := h
  have h3K : (3 : K) ≠ 0 := three_ne_zero_of_card hcard
  rw [CFSG.pRank_congr_of_mulEquiv e 3]
  refine csSup_le' ?_
  rintro r ⟨B, hB, hr⟩
  obtain ⟨hBc, hBe⟩ := (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 B).mp hB
  set E : Subgroup (GL (Fin 3) K) := B.map (CFSG.Open.StatedSU 3 (2 ^ n) K).subtype with hEdef
  have hfin : Finite E := inferInstance
  have hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg _ (congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : B) ⟨y, hy⟩))
  have hexp : ∀ x ∈ E, x ^ 3 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hBe x hx, map_one]
  have hdet : ∀ x ∈ E, (x : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    rintro _ ⟨x, -, rfl⟩
    exact CFSG.Open.StatedAPI.det_of_mem_statedSU x.2
  have hbound := CFSG.RankThree.PartTwo.Sec4.card_le_of_det_eq_one h3K (0 : Fin 3) E hcomm hexp
    hdet
  rw [Fintype.card_fin, hEdef,
    Subgroup.card_map_of_injective (CFSG.Open.StatedSU 3 (2 ^ n) K).subtype_injective, hr] at hbound
  have h32 : 3 ^ r ≤ 3 ^ 2 := by simpa using hbound
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h32


theorem isComponentOf_subgroupOf {X : Type*} [Group X] {H L : Subgroup X}
    (h : CFSG.Open.IsComponentOf L H) : CFSG.Open.IsComponentOf (L.subgroupOf H) ⊤ :=
  ⟨le_top, CFSG.Open.IsSubnormal.of_mathlib h.2.1.subgroupOf,
    CFSG.Open.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe h.1) h.2.2⟩


end CFSG.Quasithin.RonanF615
