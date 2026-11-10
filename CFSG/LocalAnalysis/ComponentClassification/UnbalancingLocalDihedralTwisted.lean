module

public import CFSG.LieType.Chevalley.GraphFixedFinitePerfect
public import CFSG.LieType.Chevalley.GraphFixedE6CommonField
public import CFSG.LieType.Chevalley.RankOneFaithful
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSASymplecticExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSCRankOneCenter

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancingLocal

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedGS

namespace DihedralTwisted

theorem nonempty_mulEquiv_graphFixedRootGroup' {T : Type} [Group T] (t : TwistTag) {p f : ℕ}
    (hp : p.Prime) (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    (hcard : Nat.card K = (p ^ f) ^ t.order) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ (p ^ f))
    (e : T ≃* DerivedCentralQuotient (twistedFixedGroup t K σ)) :
    Nonempty (T ≃* graphFixedRootGroup t K σ) := by
  have hperf := (finite_fixed_root_group_perfect t hp hf K hcard σ hσ).2.2.1
  have hZ : Subgroup.center (graphFixedRootGroup t K σ) = ⊥ :=
    center_graphFixedRootGroup_eq_bot (Finite.surjective_of_injective σ.injective)
  have hZ' : Subgroup.center ↥⁅twistedFixedGroup t K σ, twistedFixedGroup t K σ⁆ = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    have hxC : (x : ModGL t.tag K) ∈ graphFixedRootGroup t K σ := by
      rw [← hperf]
      exact x.2
    have hcen : (⟨x, hxC⟩ : graphFixedRootGroup t K σ) ∈
        Subgroup.center (graphFixedRootGroup t K σ) := by
      rw [Subgroup.mem_center_iff]
      intro y
      have hyH : (y : ModGL t.tag K) ∈ ⁅twistedFixedGroup t K σ, twistedFixedGroup t K σ⁆ := by
        rw [hperf]
        exact y.2
      have h1 := congrArg
        (Subtype.val : ↥⁅twistedFixedGroup t K σ, twistedFixedGroup t K σ⁆ → ModGL t.tag K)
        (Subgroup.mem_center_iff.1 hx ⟨y, hyH⟩)
      exact Subtype.ext h1
    rw [hZ, Subgroup.mem_bot] at hcen
    exact Subgroup.mem_bot.2
      (Subtype.ext (congrArg (Subtype.val : graphFixedRootGroup t K σ → ModGL t.tag K) hcen))
  exact ⟨e.trans ((QuotientGroup.quotientMulEquivOfEq hZ').trans
    (QuotientGroup.quotientBot.trans (MulEquiv.subgroupCongr hperf)))⟩

section Odd

variable {t : TwistTag} {K : Type} [Field K] {σ : K →+* K}


end Odd


section Two

variable {K : Type} [Field K] (σ : K →+* K)


theorem coe_orbitX_E6_zero (c : orbitField TwistTag.E6 K σ ⟨0, by decide⟩) :
    (orbitX TwistTag.E6 K σ ⟨0, by decide⟩ c : ModGL TwistTag.E6.tag K) =
      xUnit Tag.E6 K ⟨0, by decide⟩ c * xUnit Tag.E6 K ⟨5, by decide⟩ (σ c) := by
  rw [coe_orbitX]
  have hc : (TwistTag.E6.orbit ⟨0, by decide⟩).card = 2 := by decide
  have hm : TwistTag.E6.orbitMin ⟨0, by decide⟩ = ⟨0, by decide⟩ := by decide
  rw [hc, List.range_succ, List.range_succ, List.range_zero]
  simp only [List.nil_append, List.cons_append, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one, pow_zero, pow_one, hm]
  rfl

theorem coe_orbitX_E6_three (d : orbitField TwistTag.E6 K σ ⟨3, by decide⟩) :
    (orbitX TwistTag.E6 K σ ⟨3, by decide⟩ d : ModGL TwistTag.E6.tag K) =
      xUnit Tag.E6 K ⟨1, by decide⟩ d := by
  rw [coe_orbitX_of_card_eq_one (by decide)]
  have hm : TwistTag.E6.orbitMin ⟨3, by decide⟩ = ⟨1, by decide⟩ := by decide
  rw [hm]
  rfl


end Two


end DihedralTwisted

open DihedralTwisted


end CFSG.ComponentClassification.UnbalancingLocal
