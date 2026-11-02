module

public import CFSG.Monster.B.TwoA.Amalgam.FischerSliceNative
public import CFSG.Monster.B.TwoA.Fischer.CliqueKernel
public import CFSG.Monster.B.TwoA.Fischer.FullIntertwinerMain
public import CFSG.Monster.B.TwoA.Fischer.CanonicalIdent
public import CFSG.Monster.B.TwoA.Fischer.GramMinor
public import CFSG.Monster.B.TwoA.Fischer.AdjointIntertwiner
public import CFSG.Monster.B.TwoA.Fischer.AmbientRootFixed
public import CFSG.Monster.B.TwoA.Fischer.AmbientRootClique
public import CFSG.Monster.B.TwoA.Fischer.AmbientRootOrbit
public import CFSG.Monster.B.TwoA.Fischer.AmbientRootSeed
public import CFSG.Monster.B.TwoA.Fischer.AmbientRootComplete
public import CFSG.Monster.B.TwoA.Fischer.ChoiceExists

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Fischer

section Ambient

attribute [-instance] AddSubgroupClass.instZModModule

open CFSG.Monster.B.Fischer CFSG.Monster.B.Classical.Mog22 CFSG.Sporadic.SmallF2
open CFSG.Monster.B.E6.FixedE6 CFSG.Monster.B.E6.FixedE6Root CFSG.Monster.B.E6.StdF4
  CFSG.LieType.Chevalley.C2E6Std CFSG.LieType.Chevalley.C2E6Std.FieldExtension
open scoped Matrix IsMulCommutative

end Ambient

end CFSG.Monster.B.TwoA.Amalgam
