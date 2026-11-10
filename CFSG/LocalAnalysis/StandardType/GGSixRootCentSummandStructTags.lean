module

public import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandStructDerived
public import CFSG.LocalAnalysis.StandardType.GGSixLSixElevenDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21

section Tags

@[expose] def GGRootCentSummandStructTag (t : StatedLieTag) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ → GGSixStepOne p B Bs x L D J →
      GGSixStepTwo p B Bs x L D J → ∀ (E : Subgroup G) (r : G),
      GGStepThreeChoice p Bs (ggM p B x L D J) (ggU t n f).D t ψ E r →
        GGRCSStructConcl p (ggG0 p B x L D J) (ggM p B x L D J) r

theorem ggRootCentSummandStructInput_of_tags (h : ∀ t, GGRootCentSummandStructTag t) :
    GGRootCentSummandStructInput := by
  intro G _ _ p B Bs x L D J t n f ψ hctx s1 s2 E r hch
  exact h t G p B Bs x L D J n f ψ hctx s1 s2 E r hch

@[expose] def GGRootCentLayerTag (t : StatedLieTag) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p n f : ℕ) (ψ : (ggU t n f).K →* G),
    p.Prime → p ≠ 2 → StatedLieAdmissible t n 2 f → 2 ≤ (ggU t n f).D.rank →
    ψ.ker ≤ Subgroup.center (ggU t n f).K → Subgroup.centralizer (ψ.range : Set G) = ⊥ →
    GGTwoLocalRankFour p (Subgroup.normalizer (ψ.range : Set G)) →
    ∀ r : G, GGRootInvolution (ggU t n f).D t ψ r →
      GGRCSLayer p ψ.range (Subgroup.normalizer (ψ.range : Set G)) r

@[expose] def GGRootCentDerivedTag (t : StatedLieTag) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p n f : ℕ) (ψ : (ggU t n f).K →* G),
    p.Prime → p ≠ 2 → StatedLieAdmissible t n 2 f → 2 ≤ (ggU t n f).D.rank →
    ψ.ker ≤ Subgroup.center (ggU t n f).K → Subgroup.centralizer (ψ.range : Set G) = ⊥ →
    GGTwoLocalRankFour p (Subgroup.normalizer (ψ.range : Set G)) →
    ∀ r : G, GGRootInvolution (ggU t n f).D t ψ r → GGRootCentDerivedAt p ψ.range r

theorem ggRootCentLayerTag_of_derivedTag {t : StatedLieTag} (h : GGRootCentDerivedTag t) :
    GGRootCentLayerTag t := by
  intro G _ _ p n f ψ hp hp2 hadm hrk hker hC h4 r hr
  exact ggRCSLayer_of_derivedAt hp hp2 Subgroup.le_normalizer le_rfl
    (h G p n f ψ hp hp2 hadm hrk hker hC h4 r hr)

theorem ggRootCentSummandStructTag_of_layerTag {t : StatedLieTag} (h : GGRootCentLayerTag t) :
    GGRootCentSummandStructTag t := by
  intro G _ _ p B Bs x L D J n f ψ hctx s1 s2 E r hch
  have hp : p.Prime := hctx.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hctx.1.2.2.2.2.2.1.2.1
  obtain ⟨-, -, ⟨hadm, hrank⟩, ⟨hrange, hker⟩, -⟩ := hctx.2
  have hC : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by
    rw [hrange]
    exact s1.1
  have h9iii : ∀ d ∈ D, d ≠ 1 → Subgroup.centralizer {d} ≤ ggM p B x L D J := by
    intro d hd hd1 g hg
    refine s1.2.1.mem_of_conj_mem hd hd1 ?_
    have hgd : g * d = d * g := Subgroup.mem_centralizer_singleton_iff.mp hg
    have : g⁻¹ * d * g = d := by
      rw [mul_assoc, ← hgd, inv_mul_cancel_left]
    rw [this]
    exact s1.2.1.1 hd
  have h4 : GGTwoLocalRankFour p (Subgroup.normalizer (ψ.range : Set G)) := by
    rw [hrange]
    exact hctx.twoLocalRankFour h9iii
  have hlayer := h G p n f ψ hp hp2 hadm hrank hker hC h4 r hch.rootInvolution
  rw [hrange] at hlayer
  exact ggRCSStructConcl_of_layer hp hp2 hlayer

theorem ggRootCentLayerTag_of_placeholder (t : StatedLieTag)
    (ht : t = .G2 ∨ t = .trialityD4 ∨ t = .twistedB2 ∨ t = .twistedG2 ∨ t = .twistedF4 ∨
      t = .Tits) : GGRootCentLayerTag t := by
  intro G _ _ p n f ψ _ _ _ hrk
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact absurd hrk (show ¬ 2 ≤ 0 by omega)

theorem ggRootCentLayerTag_POmegaOdd : GGRootCentLayerTag .POmegaOdd :=
  fun _ _ _ _ _ _ _ _ _ hadm => absurd rfl hadm.2.2.2


end Tags

end CFSG.StandardType
