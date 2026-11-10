module

public import CFSG.ClassicalInvolution.SmallCases.Sporadic.LyAssembly
public import CFSG.ClassicalInvolution.SmallCases.SectionalFourBranch

public section

namespace CFSG.ClassicalInvolution

open CFSG.Blueprint.NativeSporadic

theorem noNonsolvableClassical_Ly : NoNonsolvableClassical (Carrier .Ly) :=
  LyProof.noNonsolvableClassical_Ly_centralizer


theorem citSectionalFour_of_gh74_models (hGH : GH74SectionalModels) :
    CFSG.ClassicalInvolution.CITSectionalFour :=
  citSectionalFour_of_gh74 noNonsolvableClassical_Ly hGH

end CFSG.ClassicalInvolution
