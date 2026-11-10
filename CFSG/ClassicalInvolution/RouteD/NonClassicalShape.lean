module

public import CFSG.ClassicalInvolution.RouteD.NonClassicalLocal
public import CFSG.ClassicalInvolution.ModelFacts.FundPerfectBridge

public section

namespace CFSG.ClassicalInvolution.RouteD.NonClassical

open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.ClassicalInvolution.RouteD.Gaps
open CFSG.Open (classicalInvolutionOddCore)

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

section Layer

variable [Finite G] {Ω : Set (Subgroup G)} {x : G}


end Layer

theorem componentFacts_of_no_exotic {X : Type} [Group X] {Φ : Set (Subgroup X)}
    (D : LieSystemData p f X Φ) (hp2 : p ≠ 2) (hq : 4 ≤ p ^ f)
    (hD : ∀ i, D.tag i ≠ .G2 ∧ D.tag i ≠ .trialityD4) :
    (∀ i, FundamentalSingleClass (D.tag i)
      (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).D) ∧
    ∀ i, FundPerfect (D.tag i) (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).D :=
  ⟨fun i => fundamentalSingleClass_of_ne D i (hD i).1 (hD i).2,
    fun i => D.fundPerfect hp2 hq (fun j hj => absurd hj (hD j).2) i⟩

@[expose] def PerpTable (p : ℕ) [Fact p.Prime] {P : Type} (rel : P → P → Prop)
    (tY : StatedLieTag) (nY : ℕ) : Prop :=
  ∀ (t : StatedLieTag) (n e : ℕ), IsFundTag t → StatedLieAdmissible t n p e →
    ∀ k : (modelUniv t n p e Fact.out).K, k ≠ 1 →
      k ^ 2 ∈ Subgroup.center (modelUniv t n p e Fact.out).K →
      (∃ R₀ ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D, k ∈ R₀) →
      ∀ φ : {R : Subgroup (modelUniv t n p e Fact.out).K //
          R ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D ∧
            R ≤ Subgroup.centralizer ({k} : Set (modelUniv t n p e Fact.out).K)} ≃ P,
        (∀ R R', Commutes R.1 R'.1 ↔ rel (φ R) (φ R')) → t = tY ∧ n = nY

theorem PerpTable.of_equiv {P P' : Type} {rel : P → P → Prop} {rel' : P' → P' → Prop}
    {tY : StatedLieTag} {nY : ℕ} (h : PerpTable p rel tY nY) (e : P ≃ P')
    (he : ∀ a b, rel a b ↔ rel' (e a) (e b)) : PerpTable p rel' tY nY := by
  intro t n e' ht hadm k hk1 hk2 hk φ hφ
  refine h t n e' ht hadm k hk1 hk2 hk (φ.trans e.symm) fun R R' => ?_
  rw [hφ R R', he]
  simp

section Shape


end Shape

end CFSG.ClassicalInvolution.RouteD.NonClassical
