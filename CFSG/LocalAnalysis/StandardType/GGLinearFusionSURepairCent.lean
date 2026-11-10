module

public import CFSG.LocalAnalysis.StandardType.GGLinearFusionSURepairBlock
public import CFSG.LocalAnalysis.StandardType.GGStdSubExistAdmissible

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank Matrix
open CFSG.SectionRank.OddCover (diagHom coe_diagHom)
open CFSG.RankThree.Classical (permGL)
open CFSG.ClassicalGroups.UnitaryFlag (unitarySU mem_unitarySU_iff)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.LieType.Universal.Unitary (SU antidiag conjTr)
open CFSG.LieType.BorelTits (unitaryInvolution)

namespace SURepair

variable {G : Type} [Group G] {n f : ℕ} {K : Type} [Field K]

@[expose] def GGFramePair (φ : ↥(unitarySU 2 f K n) →* G) (B : Subgroup G) (s t : Fin n) : Prop :=
  ∀ b ∈ B, ∀ τ : Fin n → Kˣ, SURep.GGFrameActs φ b τ → τ s = τ t

theorem mem_suPairs_of_frameActs (h : UnitaryFieldData 2 f K) {φ : ↥(unitarySU 2 f K n) →* G}
    {b : G} {τ : Fin n → Kˣ} (hb : SURep.GGFrameActs φ b τ) :
    (b, diagHom n τ) ∈ SUTorus.suPairs φ := by
  refine ⟨Subgroup.mem_normalizer_iff.mpr fun s => ⟨fun hs => SURep.conj_mem_unitarySU h hb.1 hs,
    fun hs => ?_⟩, fun u v huv => hb.2 u v huv⟩
  have h1 := SURep.conj_mem_unitarySU h (SURep.norm_inv_eq_one hb.1) hs
  have hinv : (diagHom n τ)⁻¹ = diagHom n τ⁻¹ := (map_inv _ τ).symm
  rwa [← hinv, inv_inv, show (diagHom n τ)⁻¹ * (diagHom n τ * s * (diagHom n τ)⁻¹) *
    diagHom n τ = s by group] at h1


section Core


end Core

end SURepair

section Inputs


end Inputs

end CFSG.StandardType
