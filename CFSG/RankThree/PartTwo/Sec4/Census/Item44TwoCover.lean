module

public import CFSG.RankThree.PartTwo.Sec4.Census.Item44Quasisimple
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44EndLift
import CFSG.LocalAnalysis.LyonsUnitaryFour.OrderThreeComplement
import CFSG.LocalAnalysis.SectionRank.KGroupSectionClosure
import CFSG.GroupTheory.ABGDGroups.LinearEmbedding
import CFSG.RankThree.Coprime.EvenCenterSectionCover
import CFSG.RankThree.PartTwo.NotationBlocks
import CFSG.LocalAnalysis.SectionRank.SubgroupRank

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.RankThree.PartTwo.Sec4.Census

open CFSG CFSG.Blueprint CFSG.RankThree.PartTwo Subgroup
open CFSG.Assembly.RankThreeEven (projSL localRank)

@[expose] def TwoCoverCensus : Prop :=
  ∀ (J : Type) [Group J] [Finite J], IsQuasisimple J → SectionFourHyp J →
    SectionFourHyp (J ⧸ center J) → IsPGroup 2 (center J) → Nontrivial (center J) →
    CFSG.pRank 2 J = 3 →
    (∀ q : ℕ, q.Prime → 3 < q → CFSG.pRank q (J ⧸ center J) ≤ 2) →
    (CFSG.pRank 3 (J ⧸ center J) ≤ 3 ∨ Nonempty (J ⧸ center J ≃* NativeSporadic.ON)) →
      Nonempty (J ⧸ center J ≃* NativeSporadic.M12) ∨
      (Nonempty (J ⧸ center J ≃* NativeSporadic.M22) ∧ Nat.card (center J) = 4) ∨
      Nonempty (J ⧸ center J ≃* NativeSporadic.J2) ∨
      (Nonempty (J ⧸ center J ≃* projSL 3 (GaloisField 2 2)) ∧ IsCyclic (center J) ∧
        Nat.card (center J) = 4)

theorem sectionFourHyp_subgroup {G : Type} [Group G] [Finite G] (hG : SectionFourHyp G)
    (H : Subgroup G) : SectionFourHyp H :=
  ⟨CFSG.SectionRank.K_group_section_closure_inCatalog hG.kGroup H ⊥ QuotientGroup.quotientBot,
    (evenRank_subgroup_le H).trans hG.evenRank_le,
    fun p hp h3 => (localRank_subgroup_le hp H).trans_lt (hG.localRank_lt p hp h3)⟩

noncomputable def quotientTopEquiv {G : Type} [Group G] (N : Subgroup G) [N.Normal] :
    (⊤ : Subgroup G) ⧸ N.subgroupOf ⊤ ≃* G ⧸ N :=
  QuotientGroup.congr _ _ Subgroup.topEquiv (by
    ext x
    simp [Subgroup.mem_map, Subgroup.mem_subgroupOf])

theorem sectionFourHyp_quotient (h41 : Item4_1) {G : Type} [Group G] [Finite G]
    (hG : SectionFourHyp G) (N : Subgroup G) [N.Normal] (hq : IsQuasisimple (G ⧸ N)) :
    SectionFourHyp (G ⧸ N) :=
  sectionFourHyp_of_mulEquiv (quotientTopEquiv N)
    (sectionFourHyp_of_section h41 hG ⊤ _
      (CFSG.LocalCores.isQuasisimple_of_mulEquiv (quotientTopEquiv N).symm hq))

theorem isPGroup_two_center_of_oddCore_eq_bot {X : Type*} [Group X] [Finite X]
    (hO : oddCore X = ⊥) : IsPGroup 2 (center X) := by
  intro x
  obtain ⟨a, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos (x : X)).ne'
  have hy : (x : X) ^ 2 ^ a ∈ center X := pow_mem x.2 _
  have hord : orderOf ((x : X) ^ 2 ^ a) = m := by
    rw [orderOf_pow_of_dvd (pow_ne_zero a two_ne_zero) ⟨m, hn⟩, hn]
    exact Nat.mul_div_cancel_left m (pow_pos two_pos a)
  have hle : zpowers ((x : X) ^ 2 ^ a) ≤ oddCore X := by
    refine le_oddCore (normal_of_le_center (zpowers_le.mpr hy)) ?_
    rw [Nat.card_zpowers, hord]
    exact hm
  rw [hO, le_bot_iff, zpowers_eq_bot] at hle
  exact ⟨a, Subtype.ext (by rw [Subgroup.coe_pow, hle, OneMemClass.coe_one])⟩

theorem exists_central_involution_quot {G : Type} [Group G] [Finite G] {K : Subgroup G}
    [K.Normal] (hyp : PartTwoRankThreeHyp G K) :
    ∃ z ∈ center (G ⧸ oddCore G), z ≠ 1 ∧ z * z = 1 := by
  obtain ⟨p, hp, hp5, ρ, hρ, -, a₀, ha₀2, ha₀⟩ := exists_rep hyp
  have : Fact p.Prime := ⟨hp⟩
  refine ⟨(a₀ : G ⧸ oddCore G), ?_, ?_, ?_⟩
  · rw [mem_center_iff]
    intro x
    induction x using QuotientGroup.induction_on with
    | H g =>
      have h1 : ρ (g * a₀ * (a₀ * g)⁻¹) = 1 := by
        rw [map_mul, map_inv, map_mul, map_mul, ha₀, mul_neg_one, neg_one_mul, mul_inv_cancel]
      have h2 := mk_eq_one_of_map_eq_one hρ h1
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, mul_inv_eq_one] at h2
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul] at h2
      exact h2
  · intro h
    have hneg : (-1 : GL (Fin 4) (ZMod p)) ≠ 1 := by
      intro h'
      have h'' : (-1 : Matrix (Fin 4) (Fin 4) (ZMod p)) = 1 := by
        have := congrArg (fun g : GL (Fin 4) (ZMod p) => (g : Matrix (Fin 4) (Fin 4) (ZMod p))) h'
        simpa using this
      have h00 : (-1 : Matrix (Fin 4) (Fin 4) (ZMod p)) 0 0 =
          (1 : Matrix (Fin 4) (Fin 4) (ZMod p)) 0 0 := by rw [h'']
      rw [Matrix.neg_apply, Matrix.one_apply_eq] at h00
      have h2 : ((2 : ℕ) : ZMod p) = 0 := by
        calc ((2 : ℕ) : ZMod p) = 1 - (-1) := by push_cast; ring
          _ = 0 := by rw [h00, sub_self]
      exact natCast_ne_zero_of_prime_ne Nat.prime_two (by omega) h2
    have ha₀O : a₀ ∈ oddCore G := (QuotientGroup.eq_one_iff a₀).mp h
    have ha₀1 : a₀ ≠ 1 := fun h' => hneg (by rw [← ha₀, h', map_one])
    have hord : orderOf a₀ = 2 := orderOf_eq_prime (by rw [sq, ha₀2]) ha₀1
    have := odd_orderOf_of_mem_oddCore' ha₀O
    rw [hord] at this
    exact (Nat.not_odd_iff_even.mpr even_two) this
  · rw [← QuotientGroup.mk_mul, ha₀2, QuotientGroup.mk_one]


end CFSG.RankThree.PartTwo.Sec4.Census
