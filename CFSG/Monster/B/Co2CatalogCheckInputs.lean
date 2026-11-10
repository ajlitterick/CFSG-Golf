module

public import CFSG.Monster.B.Co2CatalogData
public import Certificates.Data.CFSGNative.MonsterB.Co2Data
public import Certificates.Data.CFSGNative.MonsterB.Max2Tower
public import Certificates.Data.CFSGNative.MonsterB.BinarySha
public import Certificates.Data.CFSGNative.HS.SmallF2
public import Certificates.Data.CFSGNative.Co2.Data
public meta import CFSG.Monster.B.Co2CatalogData
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Data
public meta import Certificates.Data.CFSGNative.MonsterB.Max2Tower
public meta import Certificates.Data.CFSGNative.MonsterB.BinarySha
public meta import Certificates.Data.CFSGNative.HS.SmallF2
public meta import Certificates.Data.CFSGNative.Co2.Data
public meta import Lean.Data.Json
public import Lean.Data.Json

public section

namespace CFSG.Monster.B.Co2Catalog

open CFSG.Sporadic.SmallF2.Native CFSG.Monster.B.Binary.Native


@[expose] def quotRows (i : Nat) : Array Nat :=
  (CFSG.Monster.B.Co2.Native.genRecords[i]!).quotientMatrix

@[expose] def bridgeLetterRows (l : Int) : Array Nat :=
  if 0 < l then quotRows (l.natAbs - 1)
  else CFSG.Monster.B.Max2.Native.inv22 (quotRows (l.natAbs - 1))

@[expose] def bridgeWordRows : List Int → Array Nat
  | [] => idRows 22
  | l :: w => mulRows 22 (bridgeLetterRows l) (bridgeWordRows w)

@[expose] def bridgeCRows : Array Nat := bridgeRec.changeOfBasisRows.toArray

@[expose] def bridgeNativeArr (k : Nat) : Array Nat := (bridgeRec.nativeRows.getD k []).toArray

@[expose] def bridgeCatalogArr (k : Nat) : Array Nat :=
  (bridgeRec.catalogTransposeRows.getD k []).toArray

@[expose] def catalogRows (k : Nat) : Array Nat :=
  rowsOfPayload 22
    (if k = 0 then CFSG.Sporadic.Co2.Native.seedA else CFSG.Sporadic.Co2.Native.seedB)

end CFSG.Monster.B.Co2Catalog
