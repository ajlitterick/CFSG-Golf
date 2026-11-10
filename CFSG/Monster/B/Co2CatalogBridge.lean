module

public import CFSG.Monster.B.Co2CatalogCheck
public import CFSG.Monster.B.Co2.MatrixW
public import CFSG.Sporadic.Co2Cert.FaithfulBase

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.Co2Catalog

open CFSG.Monster CFSG.Monster.VisQuot CFSG.Monster.B.Short CFSG.Monster.B.Co2
  CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.Monster.B.Binary.Native

@[expose] noncomputable def bridgeU1 : OLq := alphaWord bridgeRec.nativeAWord

@[expose] noncomputable def bridgeU2 : OLq := alphaWord bridgeRec.nativeBWord

@[expose] noncomputable def bridgeC : Matrix (Fin 22) (Fin 22) (ZMod 2) := rowsMatrix 22 bridgeCRows

@[expose] noncomputable def bridgeNativeMat (k : ℕ) : Matrix (Fin 22) (Fin 22) (ZMod 2) :=
  rowsMatrix 22 (bridgeNativeArr k)

@[expose] noncomputable def bridgeCatalogMat (k : ℕ) : Matrix (Fin 22) (Fin 22) (ZMod 2) :=
  rowsMatrix 22 (bridgeCatalogArr k)

theorem bridgeU1_mem :
    bridgeU1 ∈ Kstab v0 := alphaWord_mem _

theorem bridgeU2_mem :
    bridgeU2 ∈ Kstab v0 := alphaWord_mem _


end CFSG.Monster.B.Co2Catalog
