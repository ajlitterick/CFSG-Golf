module

public import CFSG.Sporadic.Recognition.LyonsAmalgamTauInputs
public import CFSG.Sporadic.Recognition.LyonsModelInputs
public meta import CFSG.Sporadic.Recognition.LyonsAmalgamTauInputs
public meta import CFSG.Sporadic.Recognition.LyonsModelInputs
public meta import CFSG.Certificates.CosetTableCompactColumns
public import CFSG.Certificates.CosetTableCompactColumns
public meta import CFSG.Certificates.CosetTableShort
public import CFSG.Certificates.CosetTableShort
public meta import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.GroupTheory.LocalCores.Fitting
public meta import CFSG.Open.Defs
public import CFSG.Open.Defs

public section

namespace CFSG.Sporadic.Recognition.LyonsSims.Glue

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.SmallOddCore.Native

@[expose] def txStrings : List String :=
  ["dcdCDCdCDCDCDCdCDCdCDCdC", "dcdcdcDcDcDCdCDCdCDCdCdCdCDCDCD",
    "cdcdcdcDcDcDcdcDCdCDCdCdCdCDCDCDC", "dcdcdcdcdcdcdcDcdCDCdCDCDCDCDCDCDCD"]

@[expose] def txWords : List (List ℤ) := txStrings.map Ly0.decodeWord

@[expose] def txB : Array Table := (txWords.map (Ly0.wT Ly0.tabs0 Ly0.invs0)).toArray

@[expose] def txInvB : Array Table := txB.map (invT Ly0.deg)

@[expose] def txLetB (l : Int) : Table :=
  if 0 < l then txB[l.toNat - 1]! else txInvB[(-l).toNat - 1]!


@[expose] def lineOK (T X Xi : Table) : Bool := tblEq Ly0.deg T X || tblEq Ly0.deg T Xi


end CFSG.Sporadic.Recognition.LyonsSims.Glue
