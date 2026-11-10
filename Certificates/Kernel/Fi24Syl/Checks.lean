module

public import Certificates.Kernel.Fi24Syl.Data
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaFi24Data
import CFSG.Certificates.Kernel.Common.EachTrue
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaOrbDefs

set_option maxRecDepth 100000

#kc_each CFSG.KD.Fi24Syl fi24sylChunk
  (fun c => CFSG.KC.Fi24Syl.chunkOK CFSG.KD.Fi24Syl.tops c (CFSG.KD.Fi24Syl.stK c)) 0 27

public section

namespace CFSG.KD.Fi24Syl

open CFSG.KC.Ord CFSG.KC.Fi24Syl CFSG.AGLEmbedding.R3.AlphaFi24

theorem fi24syl_final : concl (totK stK) = true := by quickRfl

theorem fi24syl_tops :
    topsOK tops (fi24Tidx.map fun i => (fi24Mod.acts.getD i default).mat) = true := by quickRfl


end CFSG.KD.Fi24Syl

end
