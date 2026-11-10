
module

public import CFSG.Sporadic.ThSchreier.RowBase
public import CFSG.Sporadic.Th.ChainBase
public import CFSG.Sporadic.Th.Max3.PacketBase
public import CFSG.Sporadic.Th.Max3.AllConjBase
public meta import CFSG.Sporadic.ThSchreier.Text
public import CFSG.Sporadic.ThSchreier.LocalDataInputs
public import Mathlib
public import CFSG.Blueprint.NativeSporadic
public import CFSG.Blueprint.MatrixSeedIdentification
public import CFSG.Sporadic.Th.F2Spec
public import CFSG.Certificates.SchreierStabilizerGenerators
public import Certificates.Data.CFSGNative.Th.Certificate

@[expose] public section

namespace CFSG.Sporadic.ThSchreier

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3 Pointwise

@[expose] def localProgram : List Packet.Instr :=
  [.mu 1 2 3, .mu 3 2 4, .mu 3 4 5, .mu 3 5 6, .mu 6 3 7, .mu 7 4 8, .mu 3 8 9, .mu 7 9 8,
    .pwr 5 8 2, .pwr 8 3 4, .iv 4 3, .mu 3 1 5, .mu 5 4 1]


@[expose] def wRow1 : RowV :=
  toRow (rowOfNat 0xb9318bc60b06215ff4eb15e228ba41526fe75848bd0133807208caa1fa8551)

@[expose] def wRow2 : RowV :=
  toRow (rowOfNat 0x1e1057aa10c4abdf6972134ec61140ccf2027af03f80a7ed5002b65e4b1cca)

@[expose] noncomputable def planeW : Submodule (ZMod 2) RowV :=
  Submodule.span (ZMod 2) {wRow1, wRow2}


end CFSG.Sporadic.ThSchreier
