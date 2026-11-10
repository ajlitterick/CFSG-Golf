module

public import CFSG.ClassicalInvolution.AschTight.E3ModAut
public import CFSG.ClassicalInvolution.AschTight.E3OddGen

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.GorensteinWalter

section Defs

variable {G : Type} [Group G]

@[expose] def cStar (K : Subgroup G) : Subgroup G :=
  ((oddCoreQuotientAut K).comp (normalizerConj K)).ker.map (Subgroup.normalizer (K : Set G)).subtype

theorem cStar_le_normalizer (K : Subgroup G) : cStar K ≤ Subgroup.normalizer (K : Set G) :=
  Subgroup.map_subtype_le _

theorem mem_cStar_iff {K : Subgroup G} {g : G} :
    g ∈ cStar K ↔ ∃ hg : g ∈ Subgroup.normalizer (K : Set G),
      ∀ k : K, (normalizerConj K ⟨g, hg⟩ k)⁻¹ * k ∈ classicalInvolutionOddCore K := by
  constructor
  · rintro ⟨n, hn, rfl⟩
    refine ⟨n.2, fun k => ?_⟩
    have h1 := congrArg (fun α : MulAut (K ⧸ classicalInvolutionOddCore K) =>
      α (QuotientGroup.mk k)) (MonoidHom.mem_ker.mp hn)
    simp only [MonoidHom.coe_comp, Function.comp_apply, oddCoreQuotientAut_mk,
      MulAut.one_apply] at h1
    exact QuotientGroup.eq.mp h1
  · rintro ⟨hg, h⟩
    refine ⟨⟨g, hg⟩, MonoidHom.mem_ker.mpr ?_, rfl⟩
    ext x
    induction x using QuotientGroup.induction_on with
    | H k =>
      simp only [MonoidHom.coe_comp, Function.comp_apply, oddCoreQuotientAut_mk,
        MulAut.one_apply]
      exact QuotientGroup.eq.mpr (h k)


@[expose] def NormalizerQuotientTwoGeneratedStar (K : Subgroup G) : Prop :=
  ∀ P : Subgroup G, IsPGroup 2 P → P ≤ Subgroup.normalizer (K : Set G) →
    ∃ s : Finset G, s.card ≤ 2 ∧ Subgroup.closure (s : Set G) ⊔ (P ⊓ cStar K) = P

end Defs

section E3Star


end E3Star

end CFSG.ClassicalInvolution.Disconnected.AschTight
