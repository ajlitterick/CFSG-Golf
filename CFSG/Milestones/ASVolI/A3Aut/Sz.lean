module

public import CFSG.Milestones.ASVolI.A3Aut.Fam
public import CFSG.LieType.SteinbergBRSuzukiNormalizer
public import CFSG.Milestones.ASVolI.A3Aut.Util

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Blueprint CFSG.LieType.Ree CFSG.LieType.SteinbergBR
open CFSG.SignalizerFunctorTheorem.NearModels.Suzuki


section SzFamily

variable {a : ℕ} {K : Type} [Field K] [Finite K]

theorem burnsideAut_map_szFieldAut_U
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (σ : RingAut K) :
    (suzukiU a K).map (szFieldAut a K σ).toMonoidHom = suzukiU a K := by
  have hle : ∀ τ : RingAut K, (suzukiU a K).map (szFieldAut a K τ).toMonoidHom ≤ suzukiU a K := by
    intro τ
    rintro _ ⟨g, hg, rfl⟩
    obtain ⟨u, v, rfl⟩ := (mem_suzukiU_iff hK).1 hg
    change szFieldAut a K τ (suzukiSElt a K u v) ∈ suzukiU a K
    rw [szFieldAut_S]
    exact suzukiSElt_mem_suzukiU a K _ _
  refine Subgroup.eq_of_le_of_card_ge (hle σ) ?_
  rw [Subgroup.card_map_of_injective (szFieldAut a K σ).injective]


end SzFamily

end CFSG.ASVolI
