module

public import CFSG.GH74.GLS.Stage1.Thm6.Glue.L2Main
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

theorem ivkL2Facts_of_proved
    (hgen : IVK.IVK_1_2_general) (h13fc : IVK.IVK_1_3f_c) : IVKL2Facts :=
  ⟨hgen, IVK.ivk_1_2a_struct, IVK.ivk_1_2c, IVK.ivk_1_2d, IVK.ivk_1_2e, IVK.ivk_1_2f, IVK.ivk_1_2g,
    IVK.ivk_1_2h_c, IVK.ivk_1_3f_a, IVK.ivk_1_3f_b, h13fc, IVK.ivk_1_4a, IVK.ivk_1_4j⟩

end CFSG.GH74.GLS.Stage1.Thm6.Glue
