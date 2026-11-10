module

public import CFSG.ClassicalInvolution.ModelFacts.FundNoncentralSimple
public import CFSG.ClassicalInvolution.ModelFacts.FundNoncentralSp
public import CFSG.ClassicalInvolution.ModelFacts.FundNoncentralG2
public import CFSG.ClassicalInvolution.ModelFacts.FundNoncentralD4
public import CFSG.ClassicalInvolution.ModelFacts.FundNoncentralPSU
public import CFSG.ClassicalInvolution.Generic.Induction
public import CFSG.ClassicalInvolution.LBalance.Main
public import CFSG.ClassicalInvolution.Models.LinearFrames.Frame
public import CFSG.ClassicalInvolution.Models.LinearPairs
public import CFSG.ClassicalInvolution.Models.UnitaryPairs
public import CFSG.ClassicalInvolution.Models.UnitaryPairs.Pairs
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingTransport
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.PrimeComplementQuotientComponents
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Basic

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Assembly.LowTwoRank

theorem fundNoncentral_core (t : StatedLieTag) (n p e : ℕ) [hp : Fact p.Prime]
    (hfund : IsFundTag t) (hadm : StatedLieAdmissible t n p e) (hne : ¬ (t = .PSL ∧ n = 2)) :
    ∀ R ∈ fundamentalSubgroups t (modelUniv t n p e hp.out).D, ∀ r ∈ R,
      (∀ y : (modelUniv t n p e hp.out).K,
        r * y * r⁻¹ * y⁻¹ ∈ Subgroup.center (modelUniv t n p e hp.out).K) → r = 1 := by
  intro R hR r hrR hr
  have hK := isQuasisimple_modelUniv t n p e hp.out hfund hadm
  have hrc := mem_center_of_commutators_mem_center hK hr
  by_cases hPSp : t = .PSp
  · subst hPSp
    exact eq_one_of_mem_center_PSp n p e hp.out hfund hadm hR hrR hrc
  by_cases hPSU : t = .PSU
  · subst hPSU
    exact eq_one_of_mem_center_PSU n e hfund hadm R hR r hrR hrc
  by_cases hG2 : t = .G2
  · subst hG2
    exact eq_one_of_mem_center_G2 n p e hp.out hfund hadm hR hrR hrc
  by_cases hD4 : t = .trialityD4
  · subst hD4
    exact eq_one_of_mem_center_D4 n p e hp.out hfund hadm hR hrR hrc
  exact eq_one_of_mem_center_of_easy t n p e hp.out hfund hadm hne hPSp hPSU hG2 hD4 hR hrR hrc

theorem fundNoncentral_generic (p : ℕ) [Fact p.Prime] :
    ∀ (t : StatedLieTag) (n e : ℕ), CFSG.ClassicalInvolution.Generic.IsFundTag t →
      StatedLieAdmissible t n p e → ¬ (t = .PSL ∧ n = 2) →
      ∀ R ∈ CFSG.ClassicalInvolution.Generic.fundamentalSubgroups t
          (CFSG.ClassicalInvolution.Generic.modelUniv t n p e Fact.out).D,
        ∀ r ∈ R,
          (∀ y : (CFSG.ClassicalInvolution.Generic.modelUniv t n p e Fact.out).K,
            r * y * r⁻¹ * y⁻¹ ∈
              Subgroup.center (CFSG.ClassicalInvolution.Generic.modelUniv t n p e Fact.out).K) →
          r = 1 := by
  intro t n e hfund hadm hne
  have hfund' : IsFundTag t := by
    cases t <;> trivial
  exact fundNoncentral_core t n p e hfund' hadm hne

end CFSG.ClassicalInvolution.ModelFacts
