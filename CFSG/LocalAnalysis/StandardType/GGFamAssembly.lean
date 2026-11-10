module

public import CFSG.LocalAnalysis.StandardType.GGFamComponent
public import CFSG.LocalAnalysis.StandardType.GGFamTame
public import CFSG.LocalAnalysis.StandardType.GGFamFieldDispatch
public import CFSG.LocalAnalysis.StandardType.GGFamTypeAField
public import CFSG.LocalAnalysis.StandardType.GGFamInnerDispatch
public import CFSG.LocalAnalysis.StandardType.GGFamOuterDHigh
public import CFSG.LocalAnalysis.StandardType.GGFamOuterDFour
public import CFSG.LocalAnalysis.StandardType.GGFamOuterEField
public import CFSG.LocalAnalysis.StandardType.GGFamTrivial

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem langFamilyCompFieldSL_holds
    : LangFamilyCompFieldSL := by
  intro τ L _ _ _ p₀ p S hτ hp hp2 ι a hT hap K hK
  by_cases h1 : ∃ u, rootDiagUnit τ (a u) ≠ 1
  · have hTame : ∀ i : KernelComponent (famCharHom a),
        CFSG.IsQuasisimple (rationalComponentM S.ρ S.Γ (famCharHom a) i) ∨
          Group.IsSolvable (rationalComponentM S.ρ S.Γ (famCharHom a) i) :=
      fun i => langFamTame_of_prime hτ S hp hp2 hT hap h1 i
    obtain ⟨i, hKi, hq⟩ :=
      exists_eq_rationalComponentM_of_isComponentOf S hp hτ hp2 hT hap h1 hTame hK
    refine ⟨i, ?_, ?_⟩
    · rw [hKi]
      exact (Subgroup.commutator_le_self _).trans inf_le_left
    · rw [hKi]
      exact langFamRatCompFieldLenSL_of_lanes langFamRatFieldSL_typeA langFamRatFieldSL_inner
          langFamRatFieldSL_outerD_high langFamRatFieldSL_outerD_four langFamRatFieldSL_outerE τ L p₀ S hτ p hp hp2 ι a hT hap h1 i hq
  · push Not at h1
    exact langFamilyCompFieldSL_trivial hτ S a h1 K hK

end CFSG.StandardType.TableCRes
