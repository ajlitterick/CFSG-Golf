module

public import CFSG.Quasithin.Background.SimsD1FourBlocksGen
public import CFSG.LocalAnalysis.AGLEmbedding.LocalCGTBridge
import CFSG.Quasithin.EmptyFaithfulMultiple.InputD14Proof
import CFSG.Quasithin.Vol2.Ch3Sec1D12
public import CFSG.Quasithin.Background.C1PackC129Solv
public import CFSG.Quasithin.Background.SimsD1Four
public import CFSG.Quasithin.Background.SimsD1FourBlocks

public section

namespace CFSG.Quasithin.SimsD1.FourGeneral

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

theorem isKGroup_of_isSolvable (X : Type) [Group X] [Group.IsSolvable X] :
    CFSG.Open.IsKGroup X := by
  intro K L _ _ _ hnab
  obtain ⟨a, b, hab⟩ := hnab
  exact (hab ((IsSimpleGroup.comm_iff_isSolvable).mpr inferInstance a b)).elim

section Finite


end Finite

open CFSG.Quasithin.SimsD1.Transport


end CFSG.Quasithin.SimsD1.FourGeneral
