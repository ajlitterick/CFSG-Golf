module

public import Certificates.Data.CFSGNative.J4Tree.Node
public import Certificates.Data.CFSGNative.J4Tree.TreeData

public section

namespace CFSG.J4Tree.Native.Node

open CFSG.J4Tree.Native

set_option compiler.extract_closed false


@[expose] def treeParent (k : Nat) : Nat × Nat := treeParentTab[k]?.getD (0, 0)


@[expose] def globalOK : Bool :=
  treeBasis 1 == [(1131, 0)] &&
    (List.range' 1 treeN).all fun k => treeTopIds.contains k || treeTopKids.contains k ||
      (decide (1 ≤ (treeParent k).1) && decide ((treeParent k).1 < k) &&
        !(treeTopIds.contains (treeParent k).1))


end CFSG.J4Tree.Native.Node
