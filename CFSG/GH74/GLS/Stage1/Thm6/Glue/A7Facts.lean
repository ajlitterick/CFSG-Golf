module

public import CFSG.GH74.GLS.Stage1.Thm6.Glue.A7Basic
public import CFSG.GH74.GLS.IVK.Proofs
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.ClassicalGroups
public import CFSG.Dihedral.GorensteinWalter.GLSemilinearDescent
public import CFSG.GH74.GLS.Defs
public import CFSG.GH74.GLS.IVK.L2.Hilbert90Core
public import CFSG.GH74.GLS.Statements
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Critical
public import CFSG.StronglyEmbedded.MatrixGroups.PSL2

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Glue

theorem ivkA7Facts_of_proved (hf : IVK.IVK_1_1f) : IVKA7Facts :=
  ⟨IVK.ivk_1_1T, IVK.ivk_1_1a, IVK.ivk_1_1d, hf, IVK.ivk_1_1g⟩

end CFSG.GH74.GLS.Stage1.Thm6.Glue
