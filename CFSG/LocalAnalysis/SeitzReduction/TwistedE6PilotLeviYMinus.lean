module

public import CFSG.ClassicalGroups.Orthogonal.PointedPlane
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotLeviYDescent
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotLeviYGroupAction
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotModel
public import CFSG.RankThree.PartOne.KC.SymplecticSubfieldCentralizer
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotLeviYSplit

public section

namespace CFSG.SeitzReduction.TwistedE6Pilot

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Std
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
  CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.UnbalancedCatalog (semilinCentralizer mem_semilinCentralizer
  descentField mem_descentField fixSpace mem_fixSpace descentForm)

section Defs

variable {K : Type} [Field K]

@[expose] noncomputable def omegaMinusLevi (σ : K →+* K) : Subgroup (ModGL TwistTag.E6.tag K) :=
  subsystemGroup TwistTag.E6.tag K setD ⊓ graphFixedRootGroup TwistTag.E6 K σ

theorem omegaMinusLevi_le_graphFixedRootGroup (σ : K →+* K) :
    omegaMinusLevi σ ≤ graphFixedRootGroup TwistTag.E6 K σ :=
  inf_le_right

noncomputable abbrev d4Gamma (σ : K →+* K) : Subgroup (ModGL Tag.E6 K) :=
  twistedFixedGroup TwistTag.E6 K σ

noncomputable abbrev d4C0 (σ : K →+* K) : Subgroup (ModGL Tag.E6 K) :=
  graphFixedRootGroup TwistTag.E6 K σ

end Defs

section Iso


variable {K : Type} [Field K] [Finite K] [CharP K 2] {σ : K ≃+* K}
  (hσσ : ∀ c, σ (σ c) = c)
include hσσ

theorem d4Psi_mem_centralizer (g : ↥(d4Levi K ⊓ d4Gamma (σ : K →+* K))) :
    d4Psi K ⟨g, g.2.1⟩ ∈
      TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 K) ⊓ semilinCentralizer (d4Tau σ) :=
  ⟨elementaryGroup_le_orthogonalGroup _ (d4Psi_range_le ⟨_, rfl⟩),
    (mem_twistedFixedGroup_iff_d4Psi hσσ ⟨g, g.2.1⟩).1 g.2.2⟩

@[expose] noncomputable def d4FixedPsi :
    ↥(d4Levi K ⊓ d4Gamma (σ : K →+* K)) →*
      ↥(TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 K) ⊓ semilinCentralizer (d4Tau σ)) :=
  ((d4Psi K).comp (Subgroup.inclusion (inf_le_left : d4Levi K ⊓ d4Gamma (σ : K →+* K) ≤
    d4Levi K))).codRestrict _ (d4Psi_mem_centralizer hσσ)

theorem coe_d4FixedPsi (g : ↥(d4Levi K ⊓ d4Gamma (σ : K →+* K))) :
    (d4FixedPsi hσσ g : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] _) = d4Psi K ⟨g, g.2.1⟩ :=
  rfl

theorem d4FixedPsi_injective : Function.Injective (d4FixedPsi hσσ) := by
  intro g h hgh
  have h1 : d4Psi K ⟨g, g.2.1⟩ = d4Psi K ⟨h, h.2.1⟩ := congrArg Subtype.val hgh
  have h2 := d4Psi_injective h1
  exact Subtype.ext (congrArg (fun x : d4Levi K => (x : ModGL Tag.E6 K)) h2)

theorem range_d4FixedPsi :
    (d4FixedPsi hσσ).range = (orthElementaryGroup (quadPlus 4 K)).subgroupOf
      (TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 K) ⊓ semilinCentralizer (d4Tau σ)) := by
  apply le_antisymm
  · rintro _ ⟨g, rfl⟩
    rw [Subgroup.mem_subgroupOf, coe_d4FixedPsi]
    exact d4Psi_range_le ⟨_, rfl⟩
  · intro a ha
    rw [Subgroup.mem_subgroupOf, ← range_d4Psi] at ha
    obtain ⟨g, hg⟩ := ha
    have hΓ : (g : ModGL Tag.E6 K) ∈ d4Gamma (σ : K →+* K) :=
      (mem_twistedFixedGroup_iff_d4Psi hσσ g).2 (by rw [hg]; exact a.2.2)
    exact ⟨⟨g, g.2, hΓ⟩, Subtype.ext hg⟩

variable {ω : K} (hω : σ ω ≠ ω)

@[expose] noncomputable def d4FixedEquiv :
    ↥(d4Levi K ⊓ d4Gamma (σ : K →+* K)) ≃*
      ↥(elementaryGroup (quadMinus 4 (descentField σ) (d4MinusB hσσ ω) (d4MinusC hσσ ω))) :=
  ((MonoidHom.ofInjective (d4FixedPsi_injective hσσ)).trans
      (MulEquiv.subgroupCongr (range_d4FixedPsi hσσ))).trans
    ((((orthElementaryGroup (quadPlus 4 K)).subgroupOf
        (TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 K) ⊓
          semilinCentralizer (d4Tau σ))).equivMapOfInjective (d4DescentEquiv hσσ hω).toMonoidHom
        (d4DescentEquiv hσσ hω).injective).trans
      ((MulEquiv.subgroupCongr (map_d4DescentEquiv_elementary hσσ hω)).trans
        (Subgroup.subgroupOfEquivOfLe (elementaryGroup_le_orthogonalGroup _))))

include hω in
theorem isPerfect_d4Fixed : Group.IsPerfect ↥(d4Levi K ⊓ d4Gamma (σ : K →+* K)) :=
  have : Group.IsPerfect ↥(elementaryGroup (quadMinus 4 (descentField σ) (d4MinusB hσσ ω)
      (d4MinusC hσσ ω))) := (orthogonal_elementary_perfect
    (regular_quadMinus (n := 4) (K := descentField σ) (by norm_num) (d4Minus_irr hσσ hω)).1
    (regular_quadMinus (n := 4) (K := descentField σ) (by norm_num) (d4Minus_irr hσσ hω)).2).1
  Group.IsPerfect.ofSurjective (f := (d4FixedEquiv hσσ hω).symm.toMonoidHom)
    (d4FixedEquiv hσσ hω).symm.surjective

include hω in
theorem d4Fixed_le_d4C0 : d4Levi K ⊓ d4Gamma (σ : K →+* K) ≤ d4C0 (σ : K →+* K) := by
  have := isPerfect_d4Fixed hσσ hω
  rw [← Subgroup.commutator_eq_self (H := d4Levi K ⊓ d4Gamma (σ : K →+* K))]
  exact (Subgroup.commutator_mono inf_le_right inf_le_right).trans
    (commutator_twistedFixedGroup_le (t := TwistTag.E6) σ.surjective)

end Iso

section Stated

variable (k : Type) [Field k] [Finite k] [CharP k 2] (b c : k)
  (hirr : ∀ s : k, s ^ 2 + b * s + c ≠ 0)

@[expose] noncomputable def elementaryMinusStatedEquiv :
    elementaryGroup (quadMinus 4 k b c) ≃* StatedProj (StatedOmega (StatedQuadMinus 4 k b c)) :=
  ((elementaryGroup (quadMinus 4 k b c)).equivMapOfInjective
      (toLinEquiv (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) k).symm.toMonoidHom
      (toLinEquiv (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) k).symm.injective).trans
    ((MulEquiv.subgroupCongr (statedOmega_quadMinus_eq_map (n := 4) (K := k) (by norm_num)
        hirr).symm).trans
      ((QuotientGroup.quotientMulEquivOfEq
        (CFSG.SectionRank.EvenCover.statedScalars_subgroupOf_statedOmega_eq_bot
          (coe_quadMinus 4 k b c)
          ⟨(minusPair k b c (n := 4) ⟨0, by norm_num⟩).e + (minusPair k b c (n := 4) ⟨0, by norm_num⟩).f,
            by rw [CFSG.Timmesfeld.ClassicalOrders.map_add_eq_one_of_hypPair]; exact one_ne_zero⟩)).trans
        QuotientGroup.quotientBot).symm)

end Stated

section LieModel


section Fixed

variable {K : Type} [Field K] [Finite K] [CharP K 2] {σ : K ≃+* K}
  (hσσ : ∀ c, σ (σ c) = c) {ω : K} (hω : σ ω ≠ ω)
include hσσ hω

theorem omegaMinusLevi_eq :
    omegaMinusLevi (σ : K →+* K) =
      subsystemGroup TwistTag.E6.tag K setD ⊓ twistedFixedGroup TwistTag.E6 K (σ : K →+* K) := by
  apply le_antisymm
  · exact inf_le_inf_left _ (graphFixedRootGroup_le _ _ _)
  · intro g hg
    exact ⟨hg.1, d4Fixed_le_d4C0 hσσ hω hg⟩

@[expose] noncomputable def omegaMinusLeviEquiv :
    ↥(omegaMinusLevi (σ : K →+* K)) ≃*
      ↥(elementaryGroup (quadMinus 4 (descentField σ) (d4MinusB hσσ ω) (d4MinusC hσσ ω))) :=
  (MulEquiv.subgroupCongr (omegaMinusLevi_eq hσσ hω)).trans (d4FixedEquiv hσσ hω)


end Fixed

theorem lieModel_omegaMinusLevi {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K]
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    LieModel (omegaMinusLevi σ) .POmegaMinus 4 2 f := by
  have := finite_of_card hK
  have := charP_two_of_card hf hK
  obtain ⟨σE, rfl⟩ := exists_ringEquiv_toRingHom_eq σ
  have hσσ : ∀ c, σE (σE c) = c := fun c => apply_apply_eq hK hσ c
  obtain ⟨ω, hω⟩ := exists_apply_ne hf hK hσ
  have hω' : σE ω ≠ ω := hω
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf σE = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact d4_sigma_mul_self hσσ) (d4_sigma_ne_one hω')
  have hk : Nat.card (descentField σE) = 2 ^ f := by
    have h := (CFSG.RankThree.PartOne.KCSpComm.card_descentField Nat.prime_two
      (by omega : 1 ≤ 2 * f) (by rw [hK, ← pow_mul, mul_comm]) hord).2
    rwa [Nat.mul_div_cancel_left f two_pos] at h
  exact Or.inl ⟨by decide, ⟨Nat.prime_two, hf, le_rfl⟩, descentField σE, inferInstance,
    inferInstance, hk, d4MinusB hσσ ω, d4MinusC hσσ ω, d4Minus_irr hσσ hω',
    ⟨(omegaMinusLeviEquiv hσσ hω').trans
      (elementaryMinusStatedEquiv _ _ _ (d4Minus_irr hσσ hω'))⟩⟩

theorem isSimpleGroup_omegaMinusLevi {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K]
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    IsSimpleGroup (omegaMinusLevi σ) := by
  have := finite_of_card hK
  have := charP_two_of_card hf hK
  obtain ⟨σE, rfl⟩ := exists_ringEquiv_toRingHom_eq σ
  have hσσ : ∀ c, σE (σE c) = c := fun c => apply_apply_eq hK hσ c
  obtain ⟨ω, hω⟩ := exists_apply_ne hf hK hσ
  have hω' : σE ω ≠ ω := hω
  have := isSimpleGroup_statedProj_statedOmega_quadMinus (n := 4) (K := descentField σE)
    (by norm_num) (d4Minus_irr hσσ hω')
  exact ((omegaMinusLeviEquiv hσσ hω').trans
    (elementaryMinusStatedEquiv _ _ _ (d4Minus_irr hσσ hω'))).isSimpleGroup


theorem omegaMinusLevi_eq_of_card {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K]
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    omegaMinusLevi σ = subsystemGroup TwistTag.E6.tag K setD ⊓ twistedFixedGroup TwistTag.E6 K σ := by
  have := finite_of_card hK
  have := charP_two_of_card hf hK
  obtain ⟨σE, rfl⟩ := exists_ringEquiv_toRingHom_eq σ
  have hσσ : ∀ c, σE (σE c) = c := fun c => apply_apply_eq hK hσ c
  obtain ⟨ω, hω⟩ := exists_apply_ne hf hK hσ
  exact omegaMinusLevi_eq hσσ (ω := ω) hω


end LieModel

end CFSG.SeitzReduction.TwistedE6Pilot
