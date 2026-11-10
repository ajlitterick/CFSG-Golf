module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteenAInputs
import Certificates.Kernel.KDenseP.M13
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteenInputs
public import CFSG.YGroups.DCE.MaximalB
public import CFSG.YGroups.Y443.Native.AlignB
public import CFSG.YGroups.Y443.Native.AlignW
public import CFSG.YGroups.Y443.Native.CosetData
public import CFSG.YGroups.Y443.Native.Image

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

public section

namespace Certificates

open CertificateChecks

open CFSG.AGLEmbedding.Norton.MON5_7 CFSG.AGLEmbedding.Norton.GenD13
  CFSG.AGLEmbedding.Norton.MON11_13 CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteen
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThreeBNF in
theorem certificate16959 :
    gw j1W * gw j1W = 1 ∧ gw j2W * gw j2W = 1 ∧ gw j2W * gw j1W = gw j1W * gw j2W ∧
      gw j1W * gw thirteenX = gw thirteenX * gw j1W ∧
      gw j2W * gw thirteenX = gw thirteenX * gw j2W ∧
      gw tj1W * gw j1W = gw tStarW * gw tj1W ∧ gw tj2W * gw j2W = gw tStarW * gw tj2W ∧
      gw tj12W * (gw j2W * gw j1W) = gw tStarW * gw tj12W ∧
      gw j1W ≠ 1 ∧ gw j2W ≠ 1 ∧ gw j2W * gw j1W ≠ 1 ∧
      ∀ e ∈ censusLines, gw (lineConjW e) * gw (lineRepW e) =
        gw (lineTargetW e) ^ e.lam * gw (lineConjW e) := KernelKDenseP.M13.facts16959

end Certificates
