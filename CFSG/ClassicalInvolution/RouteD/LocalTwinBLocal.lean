module

public import CFSG.ClassicalInvolution.RouteD.LocalTwinPartner
public import CFSG.ClassicalInvolution.RouteD.TypeENodes
public import CFSG.ClassicalInvolution.RouteD.LocalTwinBModel

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.LieType CFSG.LieType.RootSystem CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.CurtisTits CFSG.Timmesfeld CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Generic (Commutes conjSub FundamentalSingleClass
  fundamentalSubgroups modelUniv InClass IsClassicalMember LocalOddCentral ExactMembers
  centralizingMembers)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)

variable {p f : ℕ} [Fact p.Prime]

theorem mf4_odd {m : ℕ} (hadm : StatedLieAdmissible .POmegaOdd m p f) :
    ∀ R ∈ fundamentalSubgroups .POmegaOdd (modelUniv .POmegaOdd m p f Fact.out).D,
      ∃ R' ∈ fundamentalSubgroups .POmegaOdd (modelUniv .POmegaOdd m p f Fact.out).D,
        ∃ W, LinearBlockStandardPair (GaloisField p f) W R R' := by
  refine exists_partner_fund _ (by decide) (by decide) fun γ hγ => ?_
  obtain ⟨δ, hδ, -, hW⟩ := ModelFacts.exists_standardPair_partner_POmegaOdd (p := p) (f := f) m
    hadm hγ
  exact ⟨δ, hδ, hW⟩

theorem yData_odd {m : ℕ} (hm : 3 ≤ m) (hadm : StatedLieAdmissible .POmegaOdd m p f)
    (hq : 4 ≤ p ^ f) : YData p f .POmegaOdd m := by
  obtain ⟨hf, hK⟩ := card_galoisField_of_four_le (p := p) (f := f) hq
  have hp : p.Prime := Fact.out
  have hsc : FundamentalSingleClass .POmegaOdd (modelUniv .POmegaOdd m p f Fact.out).D :=
    ModelFacts.fundamentalSingleClass .POmegaOdd m p f hp trivial hadm (by decide) (by decide)
  have hsc' : FundamentalSingleClass .POmegaOdd (oddDatum m (GaloisField p f)) := hsc
  obtain ⟨W₁, hW₁⟩ := standardPair_oddDatum_edge (F := GaloisField p f) hm (i := 0)
    (by omega)
  have hq' : 4 ≤ Nat.card (GaloisField p f) := hK ▸ hq
  have hmem := rankOne_mem_fundamentalSubgroups_oddDatum (K := GaloisField p f) hm
    (i := (⟨0, by show 0 < m; omega⟩ : Fin m)) (by show 0 + 1 < m; omega)
  refine ⟨by decide, hsc, perfectK_of_admissible hp trivial hadm, ?_, ?_, mf4_odd hadm⟩
  · exact perfect_of_mem_fundamental hsc' hmem (linearBlockStandardPair_perfect hq' hW₁).1
  · exact central_of_stdPair (p := p) (f := f) (Y := ⟨spinGroup (quadOdd m (GaloisField p f)),
      oddDatum m (GaloisField p f)⟩) hsc' hmem hW₁

theorem standardPair_oddDatum_edge' {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 3 ≤ n)
    {i j : Fin n} (h : i.val + 1 = j.val) (hj : j.val + 1 < n) :
    ∃ W, LinearBlockStandardPair F W (rankOne (oddDatum n F).rootGroup i)
      (rankOne (oddDatum n F).rootGroup j) := by
  obtain ⟨i, hi⟩ := i
  obtain ⟨j, hj'⟩ := j
  simp only at h hj
  subst h
  exact standardPair_oddDatum_edge hn (by omega)

theorem nonempty_fund_odd {m : ℕ} (hm : 3 ≤ m) :
    (fundamentalSubgroups .POmegaOdd (modelUniv .POmegaOdd m p f Fact.out).D).Nonempty :=
  ⟨_, rankOne_mem_fundamentalSubgroups_oddDatum (K := GaloisField p f) hm
    (i := (⟨0, by show 0 < m; omega⟩ : Fin m)) (by show 0 + 1 < m; omega)⟩

namespace TCtx

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G} {K : Subgroup G}


theorem exists_partner_odd {m : ℕ} (hm : 3 ≤ m) (hadm : StatedLieAdmissible .POmegaOdd m p f)
    (c : TCtx p f .POmegaOdd m Ω K z) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (hshape : LocalShapeT p f 2 .POmegaOdd m Ω z) :
    ∃ β ∈ Ω, (∃ t : G, IsClassicalMember p f β t) ∧
      (∃ W, LinearBlockStandardPair (GaloisField p f) W K β) ∧ HasFixedMember Ω K β z :=
  c.exists_partner hsingle hshape (nonempty_fund_odd hm) (mf4_odd hadm)

end TCtx

theorem TCtx.nonempty_odd {G : Type} [Group G] [Finite G] {m : ℕ} (hm : 3 ≤ m) (hp2 : p ≠ 2)
    (hq : 5 ≤ p ^ f) {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω) (hex : ExactMembers Ω)
    {K : Subgroup G} (hK : K ∈ Ω) {z : G} (hz : IsClassicalMember p f K z)
    (hP1 : LocalOddCentral Ω {z}) (hshape : LocalShapeT p f 2 .POmegaOdd m Ω z) :
    Nonempty (TCtx p f .POmegaOdd m Ω K z) := by
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  have hadm : StatedLieAdmissible .POmegaOdd m p f := ⟨Fact.out, hf, hm, hp2⟩
  have hY := yData_odd hm hadm (by omega : 4 ≤ p ^ f)
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
