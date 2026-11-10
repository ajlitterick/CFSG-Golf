module

public import CFSG.LocalAnalysis.StandardType.GGStdPosLocalDefs
import CFSG.LocalAnalysis.StandardType.GGSecFivePumpBstar
import CFSG.LocalAnalysis.StandardType.GGStdPosAutHolds

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.Steinberg

theorem ggKGCent_bstar_eq
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    {X : Subgroup G} {tg : StatedLieTag} {n f : ℕ}
    {ψ : (ggU tg n f).K →* G} (hloc : GGKGPosLocalHyp p Bs X tg n f ψ)
    (hstd : GGKGPosStdPos (ggU tg n f).D ψ Bs) :
    Bs = B := by
  obtain ⟨-, -, hadm, hrank⟩ := hloc.1
  have ht := hloc.2.1.2.2.1
  obtain ⟨-, -, xp, C, O, hE⟩ := ggStdPos_bruhatData (f := f) hrank ht
  have hr : 0 < (ggU tg n f).D.rank := by
    rw [lieUniversal_rank_eq_bnRank tg n 2 f Nat.prime_two hadm hrank]
    omega
  set γ : Fin (ggU tg n f).D.rank → ℤ := Pi.single ⟨0, hr⟩ 1
  have hγ : γ ∈ (ggU tg n f).D.roots := single_mem_roots ⟨0, hr⟩
  set T : Subgroup G := ((ggU tg n f).D.rootGroup γ).map ψ
  have hT2 : IsPGroup 2 T := (isPGroup_of_isParametrization (p := 2) hE.param hγ).map ψ
  have hT1 : T ≠ ⊥ := by
    obtain ⟨b, -, z, hz, hne⟩ := ggKGPosNoTrivRootStmt_holds G p Bs X tg n f ψ hloc hstd γ hγ
    intro hbot
    have hzT : ψ z ∈ T := Subgroup.mem_map_of_mem ψ hz
    rw [hbot, Subgroup.mem_bot] at hzT
    exact hne (by rw [hzT, mul_one, mul_inv_cancel])
  have key : ∀ c ∈ Bs, ∀ z ∈ (ggU tg n f).D.rootGroup γ, c * ψ z * c⁻¹ ∈ T := by
    intro c hc z hz
    obtain ⟨h, hh, hcz⟩ := hstd c hc γ hγ
    have hN := Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp hh γ) hγ
    rw [hcz z hz]
    exact Subgroup.mem_map_of_mem ψ ((Subgroup.mem_normalizer_iff.mp hN z).mp hz)
  refine ggBstar_eq_of_normalizes_two hcfg hT2 hT1 fun c hc => ?_
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hg
    exact key c hc z hz
  · intro hg
    obtain ⟨z, hz, hzg⟩ := Subgroup.mem_map.mp hg
    have hk := key c⁻¹ (Bs.inv_mem hc) z hz
    have e : c⁻¹ * ψ z * c⁻¹⁻¹ = g := by
      rw [hzg]
      group
    rwa [e] at hk

end CFSG.StandardType

end
