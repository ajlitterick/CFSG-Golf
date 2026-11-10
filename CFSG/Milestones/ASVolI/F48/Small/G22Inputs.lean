module

public import CFSG.Certificates.CosetTablePresented
public meta import CFSG.Certificates.CosetTablePresented
public import CFSG.Milestones.ASVolI.F48.Small.G22Base
public import CFSG.Quasithin.Recognition.CertPermList
public import CFSG.Assembly.QuasithinDefs
public import CFSG.LocalAnalysis.ComponentInitial.FieldUnitaryTrace
public import CFSG.Quasithin.Background.Basic
public import CFSG.Quasithin.Background.F2Equiv
public import CFSG.Quasithin.Recognition.CertU33AutBound
public import CFSG.Quasithin.Recognition.CertU33Phi
public import CFSG.Quasithin.Recognition.CertU33Wreath

public section

namespace CFSG.ASVolI

open CFSG.CosetTable CFSG.Quasithin

@[expose] def burnsideF48s_g22Letter (c : Char) : Fin 6 × Bool :=
  (⟨"absxyt".toList.idxOf c.toLower % 6, Nat.mod_lt _ (by norm_num)⟩, c.isLower)

@[expose] def burnsideF48s_g22Word (s : String) : List (Fin 6 × Bool) :=
  s.toList.map burnsideF48s_g22Letter


@[expose] def burnsideF48s_g22RelP1 : List String :=
  ["ss", "tt", "yyy", "aBAb", "sAsb", "aaaa", "tAtA", "bbbb",
    "ysAyB", "YtytAb", "AYBYbb", "AstsBBat"]

@[expose] def burnsideF48s_g22RelP2 : List String :=
  ["ss", "tt", "xxx", "tBtB", "bbbb", "aaaa", "bXAx", "bsAs",
    "XsXs", "aXbxb", "aaxtXtbb", "BBtstBBs"]

@[expose] def burnsideF48s_g22CandV : List String := ["STBBXa", "TBBXTaS", "SX", "STBBx"]

@[expose] def burnsideF48s_g22Cand (j : ℕ) : List (Fin 6 × Bool) :=
  (List.replicate 6 (burnsideF48s_g22Word "bTY" ++
    burnsideF48s_g22Word (burnsideF48s_g22CandV.getD j ""))).flatten

@[expose] def burnsideF48s_g22Ws (j : ℕ) : List (List (Fin 6 × Bool)) :=
  (burnsideF48s_g22RelP1 ++ burnsideF48s_g22RelP2).map burnsideF48s_g22Word ++
    [burnsideF48s_g22Cand j]

abbrev burnsideF48s_g22WsB (j : ℕ) :=
  restrictWords (subsetOf 6 [0, 1, 2, 4, 5]) (burnsideF48s_g22Ws j)


end CFSG.ASVolI
