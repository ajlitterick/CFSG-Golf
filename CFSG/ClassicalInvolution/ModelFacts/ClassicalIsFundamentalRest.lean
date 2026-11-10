module

public import CFSG.ClassicalInvolution.Generic.InductionMain
public import CFSG.ClassicalInvolution.ModelFacts.CentralLiftE6
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalPSL
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalPSU
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalSp

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank

theorem classicalIsFundamental_of_members' {p f : ℕ} [Fact p.Prime]
    (h : p ≠ 2 → 5 ≤ p ^ f → ∀ (t : StatedLieTag) (n e : ℕ) (hp : p.Prime), Generic.IsFundTag t →
      StatedLieAdmissible t n p e → (e = f ∨ (t = .trialityD4 ∧ 3 * e = f)) →
      ClassicalMembersFundamental p f t n e hp) :
    ClassicalIsFundamental p f := by
  intro hp2 hq t n e hp hFT hadm hef X _ _ ψ hψ hcen L z hL
  have : Finite (Generic.modelUniv t n p e hp).K := finite_modelUniv hp2 hp hFT hadm
  obtain ⟨L', z', hL', hmap, -⟩ := IsClassicalMember.exists_lift hp2 hq ψ hψ hcen hL
  exact ⟨L', h hp2 hq t n e hp hFT hadm hef L' z' hL', hmap.symm⟩


end CFSG.ClassicalInvolution.ModelFacts
