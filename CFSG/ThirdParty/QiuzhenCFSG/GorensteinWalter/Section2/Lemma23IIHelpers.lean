module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section1

namespace CFSG
end CFSG
open CFSG

/-!
# An odd-core inversion helper

This lower-layer helper proves a valid odd-core specialization of the
fixed-point-free inversion argument.  It predates the source correction for
Lemma 2.3(ii): the paper's actual subgroup there is
`O_{π(F(Ĥ))ᶜ}(F(M))`, not `oddCoreOf M`.  The corrected owner uses the
generic endpoint in `Section2/InvolutionInvertsOfDisjointHhat`.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u


end CFSG.GorensteinWalter
