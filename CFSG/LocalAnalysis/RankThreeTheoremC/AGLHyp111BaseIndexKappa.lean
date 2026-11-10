module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111OneSmallKappa
import CFSG.Goldschmidt.Steps.Sec82e
import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111FactorAtBase
import CFSG.LocalAnalysis.RankThreeTheoremC.D1BlockPushUp
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericFrobenius
import CFSG.LocalAnalysis.RankThreeTheoremC.TwoRest3A6CentralizingBase

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.PreuniquenessRankFour.Helpers
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem exists_maxPSubgroup_of_normalizer_le {p : ℕ} [Fact p.Prime] {Q N M : Subgroup G}
    (hQ : IsPGroup p Q) (hQN : Q ≤ N) (hQM : Q ≤ M)
    (hNorm : ∀ U : Subgroup G, Q ≤ U → U ≤ M → IsPGroup p U →
      Subgroup.normalizer (U : Set G) ≤ M) :
    ∃ T : Subgroup G, Q ≤ T ∧ T ≤ N ∧ T ≤ M ∧ IsPGroup p T ∧
      ∀ V : Subgroup G, V ≤ N → IsPGroup p V → T ≤ V → V = T := by
  classical
  set s : Set (Subgroup G) := {U | Q ≤ U ∧ U ≤ N ∧ U ≤ M ∧ IsPGroup p U} with hs
  obtain ⟨T, ⟨hQT, hTN, hTM, hT⟩, hmax⟩ :=
    Set.exists_max_image s (fun U : Subgroup G => Nat.card U) (Set.toFinite s)
      ⟨Q, le_rfl, hQN, hQM, hQ⟩
  refine ⟨T, hQT, hTN, hTM, hT, fun V hVN hV hTV => ?_⟩
  by_contra hVT
  have hlt : T.subgroupOf V ≠ ⊤ := by
    intro htop
    exact hVT (le_antisymm (Subgroup.subgroupOf_eq_top.mp htop) hTV)
  have : Group.IsNilpotent V := hV.isNilpotent
  obtain ⟨x, hxN, hxT⟩ := IsConcreteLE.exists_of_lt
    (Group.normalizerCondition_of_isNilpotent (T.subgroupOf V) (lt_top_iff_ne_top.mpr hlt))
  have hmapT : (T.subgroupOf V).map V.subtype = T := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hTV]
  have hxN' : (x : G) ∈ Subgroup.normalizer (T : Set G) := by
    have := Subgroup.le_normalizer_map V.subtype ⟨x, hxN, rfl⟩
    rwa [hmapT] at this
  set W := V ⊓ Subgroup.normalizer (T : Set G) with hW
  have hWs : W ∈ s := ⟨hQT.trans (le_inf hTV Subgroup.le_normalizer), inf_le_left.trans hVN,
    inf_le_right.trans (hNorm T hQT hTM hT), hV.to_le inf_le_left⟩
  have hTW : T ≤ W := le_inf hTV Subgroup.le_normalizer
  have hWT : W = T :=
    (Subgroup.eq_of_le_of_card_ge hTW (hmax W hWs)).symm
  have hxW : (x : G) ∈ W := ⟨x.2, hxN'⟩
  rw [hWT] at hxW
  exact hxT hxW

theorem exists_conj_le {p : ℕ} [Fact p.Prime] {P : Sylow p G} {M U : Subgroup G}
    (hPM : (P : Subgroup G) ≤ M) (hU : IsPGroup p U) (hUM : U ≤ M) :
    ∃ m ∈ M, U ≤ (P : Subgroup G).map (MulAut.conj m).toMonoidHom := by
  classical
  obtain ⟨S, hS⟩ := (hU.comap_subtype (K := M)).exists_le_sylow
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq M (P.subtype hPM) S
  refine ⟨m, m.2, fun t ht => ?_⟩
  have h1 : (⟨t, hUM ht⟩ : M) ∈ (S : Subgroup M) := hS (Subgroup.mem_subgroupOf.mpr ht)
  rw [← hm, Sylow.coe_subgroup_smul, Sylow.coe_subtype,
    Subgroup.mem_smul_pointwise_iff_exists] at h1
  obtain ⟨y, hy, hyt⟩ := h1
  refine ⟨y, Subgroup.mem_subgroupOf.mp hy, ?_⟩
  have := congrArg Subtype.val hyt
  simpa [MulAut.smul_def, MulAut.conj_apply] using this

def omegaOneCenter (p : ℕ) (U : Subgroup G) : Subgroup G where
  carrier := {x | x ∈ U ∧ (∀ u ∈ U, u * x = x * u) ∧ x ^ p = 1}
  one_mem' := ⟨U.one_mem, fun u _ => by simp, one_pow p⟩
  mul_mem' := by
    rintro x y ⟨hx, hxc, hxp⟩ ⟨hy, hyc, hyp⟩
    refine ⟨U.mul_mem hx hy, fun u hu => ?_, ?_⟩
    · rw [← mul_assoc, hxc u hu, mul_assoc, hyc u hu, mul_assoc]
    · rw [(Commute.mul_pow (hyc x hx) p), hxp, hyp, one_mul]
  inv_mem' := by
    rintro x ⟨hx, hxc, hxp⟩
    refine ⟨U.inv_mem hx, fun u hu => ?_, by rw [inv_pow, hxp, inv_one]⟩
    have := hxc u hu
    calc u * x⁻¹ = x⁻¹ * (x * u) * x⁻¹ := by group
      _ = x⁻¹ * (u * x) * x⁻¹ := by rw [this]
      _ = x⁻¹ * u := by group

theorem normalizer_le_normalizer_omegaOneCenter (p : ℕ) (U : Subgroup G) :
    Subgroup.normalizer (U : Set G) ≤ Subgroup.normalizer (omegaOneCenter p U : Set G) := by
  intro g hg
  apply Subgroup.mem_normalizer_fintype
  rintro x ⟨hx, hxc, hxp⟩
  have hgU := Subgroup.mem_normalizer_iff.mp hg
  refine ⟨(hgU x).mp hx, fun u hu => ?_, by rw [conj_pow, hxp]; group⟩
  have hu' : g⁻¹ * u * g ∈ U := by
    have := (hgU (g⁻¹ * u * g)).mpr (by simpa [mul_assoc] using hu)
    exact this
  have h := hxc _ hu'
  calc u * (g * x * g⁻¹) = g * ((g⁻¹ * u * g) * x) * g⁻¹ := by group
    _ = g * (x * (g⁻¹ * u * g)) * g⁻¹ := by rw [h]
    _ = g * x * g⁻¹ * u := by group

theorem normalizer_le_of_isAGLQ {p : ℕ} {P : Sylow p G} {M H R U : Subgroup G}
    (hext : D1Extremal p P M H R) (hU : IsAGLQ p M U) :
    Subgroup.normalizer (U : Set G) ≤ M := by
  classical
  have hp := hext.prime
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hUM, hUp, hU3⟩ := hU
  have rank3 : 3 ≤ Open.pRank p U → Subgroup.normalizer (U : Set G) ≤ M := by
    intro h3
    obtain ⟨m, hm, hUP⟩ := exists_conj_le hext.sylow_le hUp hUM
    exact (normalizer_le_weakCore p hUP (by omega)
      (h3.trans (CFSG.SectionRank.pRank_mono hp.one_lt le_sup_left))).trans
      (weakCore_conj_le hp hext.weakCore_le hm)
  by_cases h3 : 3 ≤ Open.pRank p U
  · exact rank3 h3
  rcases hU3 with h | ⟨E, hEU, hEab, hEc, hΓ⟩
  · exact absurd (by rwa [CFSG.SectionRank.pRank_coe_eq_openPRank] at h) h3
  set F := omegaOneCenter p U with hF
  have hFE : F ≤ E := by
    rintro x ⟨hx, hxc, hxp⟩
    by_contra hxE
    obtain ⟨hab, hcard⟩ := CFSG.Goldschmidt.Sec82.isElemAbelian_sup_zpowers hp hEc hEab.2 hxp hxE
      (fun e he => hxc e (hEU he))
    exact h3 (le_csSup (pRank_bddAbove p hp U)
      ⟨_, sup_le hEU ((Subgroup.zpowers_le).mpr hx), hab, hcard⟩)
  have : Nontrivial U := by
    have h1 : 1 < Nat.card U := by
      have := Subgroup.card_le_of_le hEU
      have hp2 : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) hp.one_lt
      omega
    exact Finite.one_lt_card_iff_nontrivial.mp h1
  have := hUp.center_nontrivial
  obtain ⟨n, hn, hcn⟩ := (hUp.to_subgroup (Subgroup.center U)).nontrivial_iff_card.mp inferInstance
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p (G := Subgroup.center U)
    (by rw [hcn]; exact dvd_pow_self p hn.ne')
  set x : G := ((z : U) : G) with hx
  have hxF : x ∈ F := by
    refine ⟨(z : U).2, fun u hu => ?_, ?_⟩
    · have := Subgroup.mem_center_iff.mp z.2 ⟨u, hu⟩
      exact congrArg Subtype.val this
    · have : z ^ p = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
      have := congrArg (fun w : Subgroup.center U => ((w : U) : G)) this
      simpa [hx] using this
  have hx1 : x ≠ 1 := by
    intro h
    have : z = 1 := Subtype.ext (Subtype.ext (by simpa [hx] using h))
    rw [this, orderOf_one] at hz
    exact hp.one_lt.ne hz
  have hF1 : 1 ≤ Open.pRank p F := by
    have hxp : x ^ p = 1 := hxF.2.2
    refine le_csSup (pRank_bddAbove p hp F) ⟨Subgroup.zpowers x, (Subgroup.zpowers_le).mpr hxF,
      ⟨inferInstance, fun y hy => ?_⟩, ?_⟩
    · obtain ⟨k, rfl⟩ := hy
      simp only
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hxp, one_zpow]
    · rw [Nat.card_zpowers, orderOf_eq_prime hxp hx1, pow_one]
  exact (normalizer_le_normalizer_omegaOneCenter p U).trans
    ((le_sSup ⟨F, hFE, hF1, rfl⟩ : Subgroup.normalizer (F : Set G) ≤ GLBCore p 1 E).trans hΓ)

theorem isAGLQ_of_le {p : ℕ} [Fact p.Prime] {M B U : Subgroup G} (hB : IsAGLQ p M B)
    (hBU : B ≤ U) (hUM : U ≤ M) (hU : IsPGroup p U) : IsAGLQ p M U := by
  obtain ⟨-, -, h | ⟨E, hEB, hE⟩⟩ := hB
  · refine ⟨hUM, hU, Or.inl ?_⟩
    rw [CFSG.SectionRank.pRank_coe_eq_openPRank] at h ⊢
    exact h.trans (CFSG.SectionRank.pRank_mono (Fact.out : p.Prime).one_lt hBU)
  · exact ⟨hUM, hU, Or.inr ⟨E, hEB.trans hBU, hE⟩⟩


end CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
