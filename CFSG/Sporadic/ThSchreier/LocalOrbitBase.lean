
module

public import CFSG.Sporadic.ThSchreier.LocalDataBase
public import CFSG.Sporadic.ThSchreier.WordsBase
public meta import CFSG.Sporadic.ThSchreier.WordsBase
public meta import CFSG.Sporadic.ThSchreier.LocalDataBase
public import CFSG.Sporadic.ThSchreier.LocalOrbitInputs
public import Mathlib
public import CFSG.Blueprint.NativeSporadic
public import CFSG.Blueprint.MatrixSeedIdentification
public import CFSG.Sporadic.Th.F2Spec
public import CFSG.Certificates.SchreierStabilizerGenerators
public import Certificates.Data.CFSGNative.Th.Certificate
public import CFSG.Sporadic.Th.Max3.DataBase

@[expose] public section

namespace CFSG.Sporadic.ThSchreier

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3 Pointwise


theorem planeW_coe : (planeW : Set RowV) = {0, wRow1, wRow2, wRow1 + wRow2} := span_pair_eq _ _

theorem rowPlane_wKeyRow : rowPlane wKeyRow = planeW := by
  rw [planeW_coe, wKeyRow, rowPlane_canon, toVec_v4OfNat, toVec_v4OfNat]
  rfl


end CFSG.Sporadic.ThSchreier
