module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoDefs
public import Certificates.Certificate31063
public import CFSG.LocalAnalysis.RankThreeTheoremC.CoreGenerationOne
public import Certificates.Data.CoreD2LinesOne
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CoreD2Ru
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFact2314Abstract
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoSporCore
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoSporMax
import CFSG.Quasithin.Background.A318POutMore
import CFSG.RankThree.PartTwo.Sec4.Item47Native
import CFSG.Sporadic.Bridge.RuSurj
public import CFSG.Sporadic.Schreier.RuCentralizer

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

open CFSG.Open Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four CFSG.AGLEmbedding.FusD2
  CFSG.AGLEmbedding.CoreD2 Certificates.CoreD2Perm
open Certificates.FusD2Perm (powT wordT)

section Abstract

theorem CoreGenerationOneOf.of_mulEquiv {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
    {p : ℕ} (hp : p.Prime) (e : G ≃* H) (h : CoreGenerationOneOf G p) :
    CoreGenerationOneOf H p := by
  obtain ⟨E, hEc, hEexp, hEnab, hall⟩ := h
  refine ⟨E.map e.toMonoidHom, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective e.injective, hEc]
  · rintro _ ⟨x, hx, rfl⟩
    simpa using congrArg e (hEexp x hx)
  · obtain ⟨x, hx, y, hy, hxy⟩ := hEnab
    exact ⟨e x, ⟨x, hx, rfl⟩, e y, ⟨y, hy, rfl⟩, fun h => hxy (e.injective (by simpa using h))⟩
  · intro A' hA'E hA'e hA'c
    set A : Subgroup G := A'.map e.symm.toMonoidHom with hAdef
    have hAE : A ≤ E := by
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.1 (hA'E hy)
      have : e.symm.toMonoidHom y = x := by
        rw [← hxy]
        exact e.symm_apply_apply x
      rwa [this]
    have hAe : IsElemAbelian p A := CFSG.SectionRank.isElemAbelian_map hA'e _
    have hAc : Nat.card A = p ^ 2 := by
      rw [hAdef, Subgroup.card_map_of_injective e.symm.injective, hA'c]
    obtain ⟨Γ, hΓ, hnorm⟩ := hall A hAE hAe hAc
    refine ⟨e.toMonoidHom '' Γ, ?_, ?_⟩
    · rw [← MonoidHom.map_closure, hΓ, Subgroup.map_top_of_surjective _ e.surjective]
    · rintro _ ⟨g, hg, rfl⟩
      obtain ⟨Q, hQA, hrank, hgQ⟩ := hnorm g hg
      refine ⟨Q.map e.toMonoidHom, ?_, ?_, ?_⟩
      · rintro _ ⟨q, hq, rfl⟩
        obtain ⟨x, hx, hxq⟩ := Subgroup.mem_map.1 (hQA hq)
        have : e.toMonoidHom q = x := by
          rw [← hxq]
          exact e.apply_symm_apply x
        rwa [this]
      · exact hrank.trans (CFSG.SectionRank.pRank_le_map hp.one_lt e.toMonoidHom e.injective Q)
      · rw [← Subgroup.map_equiv_normalizer_eq]
        exact Subgroup.mem_map_of_mem _ hgQ

theorem sylow_facts_of_coreGenerationOneOf {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] (h : CoreGenerationOneOf G p) (hS : ∀ T : Sylow p G, Nat.card T = p ^ 3)
    (S : Sylow p G) :
    Nat.card (S : Subgroup G) = p ^ 3 ∧ (∀ x ∈ (S : Subgroup G), x ^ p = 1) ∧
      (∃ x ∈ (S : Subgroup G), ∃ y ∈ (S : Subgroup G), x * y ≠ y * x) ∧
      ∀ A : Subgroup G, A ≤ S → IsElemAbelian p A → Nat.card A = p ^ 2 →
        GLBCore p 1 A = ⊤ := by
  have hp : p.Prime := Fact.out
  obtain ⟨E, hEc, hEexp, hEnab, hall⟩ := h
  have hEp : IsPGroup p E := IsPGroup.of_card hEc
  obtain ⟨T₀, hET⟩ := hEp.exists_le_sylow
  have hET0 : (T₀ : Subgroup G) = E :=
    (Subgroup.eq_of_le_of_card_ge hET (by rw [hEc, hS T₀])).symm
  obtain ⟨l, -, hl⟩ := CFSG.AGLEmbedding.exists_mem_map_conj_eq_of_card_eq
    (L := ⊤) (le_top : (S : Subgroup G) ≤ ⊤) le_top S.isPGroup' T₀.isPGroup'
    (by
      change ¬ p ∣ (S : Subgroup G).relIndex ⊤
      rw [Subgroup.relIndex_top_right]
      exact S.not_dvd_index)
    (by rw [Sylow.card_eq_multiplicity T₀, Sylow.card_eq_multiplicity S])
  rw [hET0] at hl
  refine ⟨hS S, fun x hx => ?_, ?_, fun A hAS hAe hA => ?_⟩
  · have hx' : l * x * l⁻¹ ∈ E := by
      rw [← hl]
      exact ⟨x, hx, rfl⟩
    have h1 := hEexp _ hx'
    rw [conj_pow, mul_inv_eq_one, mul_eq_left] at h1
    exact h1
  · obtain ⟨x, hx, y, hy, hxy⟩ := hEnab
    rw [← hl] at hx hy
    obtain ⟨x', hx', rfl⟩ := hx
    obtain ⟨y', hy', rfl⟩ := hy
    refine ⟨x', hx', y', hy', fun h => hxy ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [show l * x' * l⁻¹ * (l * y' * l⁻¹) = l * (x' * y') * l⁻¹ by group, h]
    group
  · have hA' : A.map (MulAut.conj l).toMonoidHom ≤ E := by
      rw [← hl]
      exact Subgroup.map_mono hAS
    have hAe' : IsElemAbelian p (A.map (MulAut.conj l).toMonoidHom) :=
      CFSG.SectionRank.isElemAbelian_map hAe _
    have hAc' : Nat.card (A.map (MulAut.conj l).toMonoidHom) = p ^ 2 := by
      rw [Subgroup.card_map_of_injective (MulAut.conj l).injective, hA]
    obtain ⟨Γ, hΓ, hnorm⟩ := hall _ hA' hAe' hAc'
    have hle : (⊤ : Subgroup G) ≤ GLBCore p 1 (A.map (MulAut.conj l).toMonoidHom) := by
      rw [← hΓ, Subgroup.closure_le]
      intro g hg
      obtain ⟨Q, hQA, hrank, hgQ⟩ := hnorm g hg
      exact CFSG.AGLEmbeddingD2.normalizer_le_glbCore p 1 hQA hrank hgQ
    have hAA : (A.map (MulAut.conj l).toMonoidHom).map (MulAut.conj l⁻¹).toMonoidHom = A :=
      map_conj_inv_map_conj A l
    have h1 := glbCore_le_comap_conj p 1 hp l⁻¹ hAA
    rw [eq_top_iff]
    intro x _
    have hx := h1 (hle (Subgroup.mem_top (l * x * l⁻¹)))
    rw [Subgroup.mem_comap] at hx
    simpa [MulAut.conj_apply, mul_assoc] using hx

end Abstract

section Perm


end Perm

section Ru

open CFSG.Sporadic.RuSchreier

theorem coreGenerationOneOf_ruP :
    CoreGenerationOneOf ↥ruP 5 :=
  Certificates.certificate31063

private theorem card_sylow_five_of_card {K : Type*} [Group K] [Finite K]
    (hK : Nat.card K = 145926144000) (T : Sylow 5 K) : Nat.card T = 5 ^ 3 := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have h0 : (145926144000 : ℕ) ≠ 0 := by norm_num
  have h1 := (Nat.prime_five.pow_dvd_iff_le_factorization h0).1
    (by norm_num : 5 ^ 3 ∣ 145926144000)
  have h2 : ¬ 4 ≤ (145926144000 : ℕ).factorization 5 := fun h => by
    have := (Nat.prime_five.pow_dvd_iff_le_factorization h0).2 h
    norm_num at this
  rw [Sylow.card_eq_multiplicity T, hK, show (145926144000 : ℕ).factorization 5 = 3 by omega]

theorem threeFourTwoNoneAt_ru :
    ThreeFourTwoNoneAt 5 (TauCeti.CFSGIndex.sporadic .Ru).Group := by
  have hcard : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .Ru) = 145926144000 :=
    CFSG.Sporadic.Ru.card_Ru
  haveI : Finite (CFSG.Blueprint.NativeSporadic.Carrier .Ru) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hO : Nat.card (Outer (CFSG.Blueprint.NativeSporadic.Carrier .Ru)) ≤ 2 :=
    CFSG.RankThree.PartTwo.Sec4.card_outer_Ru
  obtain ⟨hX, hnab, hout⟩ := sporadicIndex_facts_of_bridge (s := .Ru)
    CFSG.Sporadic.Bridge.Ru.nonempty_mulEquiv CFSG.Sporadic.Ru.isSimpleGroup_Ru hO
    Nat.prime_five (by rw [hcard]; norm_num)
  refine threeFourTwoNoneAt_of_glbCore_eq_top hX hnab hout fun K _ _ hK => ?_
  obtain ⟨e⟩ := nonempty_mulEquiv_carrier_of_sporadicIndex (s := .Ru)
    CFSG.Sporadic.Bridge.Ru.nonempty_mulEquiv hK
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hKc : Nat.card K = 145926144000 := by rw [Nat.card_congr e.toEquiv, hcard]
  have hcg : CoreGenerationOneOf K 5 :=
    coreGenerationOneOf_ruP.of_mulEquiv Nat.prime_five (e.trans ruEquivP).symm
  refine ⟨CFSG.Quasithin.A318P.not_dvd_outer_Ru e Nat.prime_five (by norm_num), fun T => ?_⟩
  obtain ⟨hTc, hTexp, hTnab, hTA⟩ :=
    sylow_facts_of_coreGenerationOneOf hcg (card_sylow_five_of_card hKc) T
  refine ⟨hTc, hTexp, hTnab, ?_, hTA⟩
  have hsurj : Function.Surjective e.toMonoidHom := e.surjective
  set S : Sylow 5 (CFSG.Blueprint.NativeSporadic.Carrier .Ru) := T.mapSurjective hsurj with hS
  have hST : (S : Subgroup _).map e.symm.toMonoidHom = T := by
    rw [hS, Sylow.coe_mapSurjective, Subgroup.map_map]
    convert Subgroup.map_id (T : Subgroup K)
    ext x
    simp
  rw [← hST]
  exact CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Fact2314.glbCore_map_eq_top_of_injOn
    Nat.prime_five e.symm.toMonoidHom e.symm.surjective
    (fun x _ hx => e.symm.injective (by simpa using hx)) (CFSG.AGLEmbedding.glbCore_Ru_five S)

end Ru

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen
