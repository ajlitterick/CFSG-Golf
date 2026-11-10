module

public import CFSG.ClassicalInvolution.RouteD.LocalTwinPartner
public import CFSG.ClassicalInvolution.RouteD.TypeENodes
public import CFSG.ClassicalInvolution.RouteD.TypeDRecognition

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.LieType CFSG.LieType.RootSystem CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.CurtisTits CFSG.Timmesfeld CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Generic (Commutes conjSub FundamentalSingleClass
  fundamentalSubgroups modelUniv InClass IsClassicalMember LocalOddCentral ExactMembers
  centralizingMembers)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)

variable {p f : ℕ} [Fact p.Prime]

theorem mf4_plus {m : ℕ} (hadm : StatedLieAdmissible .POmegaPlus m p f) :
    ∀ R ∈ fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus m p f Fact.out).D,
      ∃ R' ∈ fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus m p f Fact.out).D,
        ∃ W, LinearBlockStandardPair (GaloisField p f) W R R' := by
  refine exists_partner_fund _ (by decide) (by decide) fun γ hγ => ?_
  obtain ⟨δ, hδ, -, hW⟩ := ModelFacts.exists_standardPair_partner_POmegaPlus (p := p) (f := f) m
    hadm hγ
  exact ⟨δ, hδ, hW⟩

theorem yData_plus {m : ℕ} (hm : 4 ≤ m) (hadm : StatedLieAdmissible .POmegaPlus m p f)
    (hq : 4 ≤ p ^ f) : YData p f .POmegaPlus m := by
  obtain ⟨hf, hK⟩ := card_galoisField_of_four_le (p := p) (f := f) hq
  have hp : p.Prime := Fact.out
  have hm3 : 3 ≤ m := by omega
  have hsc : FundamentalSingleClass .POmegaPlus (modelUniv .POmegaPlus m p f Fact.out).D :=
    ModelFacts.fundamentalSingleClass .POmegaPlus m p f hp trivial hadm (by decide) (by decide)
  have e := modelUniv_POmegaPlus_eq (p := p) (f := f) hm3
  have hsc' : FundamentalSingleClass .POmegaPlus (plusDatum m (GaloisField p f) hm3) := by
    revert hsc; rw [e]; exact id
  obtain ⟨-, W₁, hW₁⟩ := ModelFacts.standardPair_plusDatum (F := GaloisField p f) hm3 hm
  have hq' : 4 ≤ Nat.card (GaloisField p f) := hK ▸ hq
  refine ⟨by decide, hsc, perfectK_of_admissible hp trivial hadm, ?_, ?_, mf4_plus hadm⟩
  · rw [e]
    exact perfect_of_mem_fundamental hsc'
      (rankOne_mem_fundamentalSubgroups_plusDatum hm3 (⟨0, by show 0 < m; omega⟩ : Fin m))
      (linearBlockStandardPair_perfect hq' hW₁).1
  · rw [e]
    exact central_of_stdPair (p := p) (f := f) (Y := ⟨spinGroup (quadPlus m (GaloisField p f)),
      plusDatum m (GaloisField p f) hm3⟩) hsc'
      (rankOne_mem_fundamentalSubgroups_plusDatum hm3 (⟨0, by show 0 < m; omega⟩ : Fin m)) hW₁

theorem nonempty_fund_plus {m : ℕ} (hm : 4 ≤ m) :
    (fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus m p f Fact.out).D).Nonempty := by
  have hm3 : 3 ≤ m := by omega
  rw [modelUniv_POmegaPlus_eq (p := p) (f := f) hm3]
  exact ⟨_, rankOne_mem_fundamentalSubgroups_plusDatum hm3 (⟨0, by show 0 < m; omega⟩ : Fin m)⟩

namespace TCtx

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G} {K : Subgroup G}


theorem exists_partner_plus {m : ℕ} (hm : 4 ≤ m) (hadm : StatedLieAdmissible .POmegaPlus m p f)
    (c : TCtx p f .POmegaPlus m Ω K z) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (hshape : LocalShapeT p f 2 .POmegaPlus m Ω z) :
    ∃ β ∈ Ω, (∃ t : G, IsClassicalMember p f β t) ∧
      (∃ W, LinearBlockStandardPair (GaloisField p f) W K β) ∧ HasFixedMember Ω K β z :=
  c.exists_partner hsingle hshape (nonempty_fund_plus hm) (mf4_plus hadm)

end TCtx

theorem TCtx.nonempty_plus {G : Type} [Group G] [Finite G] {m : ℕ} (hm : 4 ≤ m) (hp2 : p ≠ 2)
    (hq : 5 ≤ p ^ f) {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω) (hex : ExactMembers Ω)
    {K : Subgroup G} (hK : K ∈ Ω) {z : G} (hz : IsClassicalMember p f K z)
    (hP1 : LocalOddCentral Ω {z}) (hshape : LocalShapeT p f 2 .POmegaPlus m Ω z) :
    Nonempty (TCtx p f .POmegaPlus m Ω K z) := by
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  have hadm : StatedLieAdmissible .POmegaPlus m p f := ⟨Fact.out, hf, by show 4 ≤ m; omega⟩
  have hY := yData_plus hm hadm (by omega : 4 ≤ p ^ f)
  obtain ⟨d⟩ := hshape.nonempty_dictT2 hY.ne_d4 hY.sc hΩ hK hz
  obtain ⟨d', hQ⟩ := exists_dictT2_of_member hY hK hz d
  exact ⟨{
    hp2 := hp2
    hq := hq
    hΩ := hΩ
    hex := hex
    hK := hK
    hz := hz
    hP1 := hP1
    d := d'
    hQ₀ := hQ
    hY := hY }⟩

end CFSG.ClassicalInvolution.RouteD
