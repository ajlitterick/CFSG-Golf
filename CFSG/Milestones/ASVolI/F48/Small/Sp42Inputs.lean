module

public import CFSG.Certificates.CosetTablePresented
public meta import CFSG.Certificates.CosetTablePresented
public import CFSG.Milestones.ASVolI.F48.Small.EngCheck
public meta import Mathlib
public import Mathlib

public section

namespace CFSG.ASVolI

open CFSG.CosetTable

@[expose] def burnsideF48s_sp42Letter (c : Char) : Fin 5 × Bool :=
  (⟨"abcde".toList.idxOf c.toLower % 5, Nat.mod_lt _ (by norm_num)⟩, c.isLower)

@[expose] def burnsideF48s_sp42Word (s : String) : List (Fin 5 × Bool) :=
  s.toList.map burnsideF48s_sp42Letter

@[expose] def burnsideF48s_sp42RelA : List String :=
  ["aa", "dd", "bb", "bCbC", "aCac", "abab", "adad", "dcbdcc", "dbdbdb"]

@[expose] def burnsideF48s_sp42RelB : List String :=
  ["bb", "aa", "ee", "beae", "caCa", "baba", "cccc", "bCbC", "ceCeCea", "bCCaecce"]

@[expose] def burnsideF48s_sp42CandA : List String := ["D", "D", "AD", "AD"]

@[expose] def burnsideF48s_sp42CandB : List String := ["E", "ECCB", "E", "ECCB"]

@[expose] def burnsideF48s_sp42Ext (j : ℕ) : List (Fin 5 × Bool) :=
  (List.replicate 4 (burnsideF48s_sp42Word (burnsideF48s_sp42CandA.getD j "") ++
    burnsideF48s_sp42Word (burnsideF48s_sp42CandB.getD j ""))).flatten

@[expose] def burnsideF48s_sp42Ws (j : ℕ) : List (List (Fin 5 × Bool)) :=
  (burnsideF48s_sp42RelA ++ burnsideF48s_sp42RelB).map burnsideF48s_sp42Word ++
    [burnsideF48s_sp42Ext j]

abbrev burnsideF48s_sp42WsA (j : ℕ) :=
  restrictWords (subsetOf 5 [0, 1, 2, 3]) (burnsideF48s_sp42Ws j)


end CFSG.ASVolI
