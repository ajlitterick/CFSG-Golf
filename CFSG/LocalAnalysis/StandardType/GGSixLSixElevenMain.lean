module

public import CFSG.LocalAnalysis.StandardType.GGSixLSixElevenDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

section Inputs

theorem GGSixFusionSetting.linear_or_triality (hKG : GGSixLSixElevenKGInput) {G : Type}
    [Group G] [Finite G] {p : ℕ} {Bs G₀ : Subgroup G} {t : StatedLieTag} {n f : ℕ}
    {ψ : (ggU t n f).K →* G} (hS : GGSixFusionSetting p Bs G₀ (ggU t n f).D t n f ψ)
    (hR : GGTwoLocalRankFour p (Subgroup.normalizer (G₀ : Set G))) {b : G} (hb : b ∈ Bs)
    (hC : Subgroup.centralizer {b} ≤ Subgroup.normalizer (G₀ : Set G)) {g : G}
    (hg : g⁻¹ * b * g ∈ Subgroup.normalizer (G₀ : Set G))
    (hgM : g ∉ Subgroup.normalizer (G₀ : Set G)) :
    GGSixLinearCase p t n f ∨ GGTrialityCaseAt p G₀ (ggU t n f).D t n f ψ (g⁻¹ * b * g) :=
  hKG G p Bs G₀ t n f ψ hS hR b hb (g⁻¹ * b * g) hg
    (hS.orderOf_conj hb (ne_one_of_centralizer_le hC hgM) g) (hS.not_conj_mem hb hC hgM)
    (ggCentralizerEmbeds_conj hC)


theorem ggSixLSixElevenInput_of_kg (hKG : GGSixLSixElevenKGInput)
    (hR : GGSixTwoLocalRankInput) : GGSixLSixElevenInput := by
  intro G _ _ p B Bs x L D J t n f ψ hctx hC hU b hb hCb g hg hgM
  exact (hctx.fusionSetting hC hU).linear_or_triality hKG (hR G p B Bs x L D J t n f ψ hctx hC hU)
    hb hCb hg hgM


end Inputs

end CFSG.StandardType
