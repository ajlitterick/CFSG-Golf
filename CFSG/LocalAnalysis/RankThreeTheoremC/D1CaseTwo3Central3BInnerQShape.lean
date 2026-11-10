module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3Central3BInnerSplit
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoEscapeAux

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

namespace InnerQ

open CFSG.Open CFSG.AGLEmbedding CFSG.PreuniquenessRankFour.Helpers CFSG.QuasithinUnique
  CFSG.RankThreeCoreUniqueness.Helpers
open scoped commutatorElement

theorem pRank_top_le_one_of_isCyclic {p : ℕ} {K : Type*} [Group K] [Finite K] [Fact p.Prime]
    (T : Sylow p K) (hT : IsCyclic (T : Subgroup K)) : Open.pRank p (⊤ : Subgroup K) ≤ 1 := by
  have hp : p.Prime := Fact.out
  obtain ⟨E, -, hE, hEcard⟩ := pRank_attained p hp (⊤ : Subgroup K)
  have hle := card_le_of_isElemAbelian_of_isCyclic_sylow T hT hE
  rw [hEcard] at hle
  by_contra hlt
  push_neg at hlt
  have : p ^ 2 ≤ p ^ Open.pRank p (⊤ : Subgroup K) := Nat.pow_le_pow_right hp.pos hlt
  have : p < p ^ 2 := by nlinarith [hp.two_le]
  omega


theorem not_gamma_le_of_two_components {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {M H E : Subgroup G} {L L' : Subgroup (H ⧸ primeComplementCore (G := H) p)}
    (hL : IsComponentOf L ⊤) (hL' : IsComponentOf L' ⊤) (hne : L ≠ L')
    (hL'X : ¬ L' ≤ d1X0 p M H) (hE : IsElemAbelian p E)
    (hEL : (E.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) ⊓ L ≠ ⊥) :
    ¬ rankThreeGamma 1 p E ≤ M := by
  intro hΓ
  have : Fact p.Prime := ⟨hp⟩
  set π := QuotientGroup.mk' (primeComplementCore (G := H) p)
  obtain ⟨⟨y, hy⟩, hne1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hEL
  obtain ⟨⟨e, heE, rfl⟩, heL⟩ := hy
  have heE' : (e : G) ∈ E := heE
  have hep : (e : G) ^ p = 1 := hE.2 _ heE'
  have he1 : (e : G) ≠ 1 := by
    intro h1
    apply hne1
    have : e = 1 := Subtype.ext h1
    exact Subtype.ext (by simp [this])
  have hord : orderOf (e : G) = p := orderOf_eq_prime hep he1
  have hordH : orderOf e = p := (Subgroup.orderOf_coe e).symm.trans hord
  have heP : IsPGroup p (Subgroup.zpowers e) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hordH, pow_one])
  have hN : Subgroup.normalizer ((Subgroup.zpowers (e : G) : Subgroup G) : Set G) ≤ M := by
    refine le_trans ?_ hΓ
    refine le_sSup ⟨Subgroup.zpowers (e : G), Subgroup.zpowers_le.mpr heE', ?_, rfl⟩
    exact le_csSup (pRank_bddAbove p hp _) ⟨Subgroup.zpowers (e : G), le_rfl,
      isElemAbelian_zpowers hep, by rw [Nat.card_zpowers, hord, pow_one]⟩
  apply hL'X
  intro l hl
  have hcomm : l ∈ Subgroup.centralizer ({π e} : Set (H ⧸ primeComplementCore (G := H) p)) := by
    have hc : ⁅L, L'⁆ = ⊥ := by
      rcases CFSG.LocalCores.distinct_components_commute ((CFSG.isComponent_iff_open L).mpr hL)
        ((CFSG.isComponent_iff_open L').mpr hL') with h | h
      · exact absurd h hne
      · exact h
    have hmem : ⁅π e, l⁆ ∈ ⁅L, L'⁆ := Subgroup.commutator_mem_commutator heL hl
    rw [hc, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    exact Subgroup.mem_centralizer_singleton_iff.mpr hmem.symm
  obtain ⟨g, hg, hgl⟩ := exists_mem_centralizer_mk_eq hp _ (primeComplementCore_coprime p) heP hcomm
  have hgC : (g : G) ∈ Subgroup.normalizer ((Subgroup.zpowers (e : G) : Subgroup G) : Set G) := by
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    have hge : g * e = e * g := (Subgroup.mem_centralizer_singleton_iff.mp hg)
    have hge' : (e : G) * g = g * e := by
      have := congrArg Subtype.val hge
      simpa [Subgroup.coe_mul] using this.symm
    exact ((Commute.zpow_left hge' k).eq)
  exact ⟨g, Subgroup.mem_subgroupOf.mpr ⟨g.2, hN hgC⟩, hgl⟩

end InnerQ

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers


end CFSG.LocalAnalysis.RankThreeTheoremC
