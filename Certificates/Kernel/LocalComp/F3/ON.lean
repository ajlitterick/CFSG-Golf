module

public import Certificates.Kernel.LocalComp.LaySeeds
public import Certificates.Data.Kernel.OpsLayKNorm
public import Certificates.Data.CFSGNative.Filter.ONData
public import Certificates.Data.CFSGNative.MultRes.Witnesses
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeCubData
import all CFSG.Blueprint.NativeSporadic

set_option maxRecDepth 400000

#lay_seeds CFSG.KD.LC.F3.ON 3 154
  CFSG.Blueprint.NativeSporadic.ONSeed1 CFSG.Blueprint.NativeSporadic.ONSeed2

public section

namespace CFSG.KD.LC.F3.ON

open CFSG.KC.OpsLayK CFSG.SectionRank.Native

theorem sec_K : secK lay A B onanSec = true := by decide +kernel

theorem mult_K : cubK lay A B onMultData = true := by decide +kernel

theorem norm_K : normCK lay A B onNormData = true := by decide +kernel

theorem sylow7H_K : cubK lay A B CFSG.AGLEmbedding.SporCubic.onSylow7HData = true := by
  decide +kernel


end CFSG.KD.LC.F3.ON

end
