module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCoverCertInputs
public import Certificates.Data.GrSLitL34FactsRealReps
public import CFSG.Certificates.CosetTableShort
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions
public import CFSG.Open.Defs

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts.Real

open CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34 CFSG.CosetTable
open CFSG.ComponentClassification.GrSLit.L34Facts

@[expose] def rTab (w : List ℕ) : Tab := w.foldl (fun t j => comp 42 t gTabs[j]!) (idTab 42)

@[expose] def repTab (i : ℕ) : Tab := rTab (realRepWords.getD i [])

@[expose] def uA (i : ℕ) : List (Fin 2 × Bool) := parseWord (realRepU.getD i ("", "")).1

@[expose] def uB (i : ℕ) : List (Fin 2 × Bool) := parseWord (realRepU.getD i ("", "")).2

@[expose] def aut (i : ℕ) : List (List (Fin 2 × Bool)) := autWs (uA i) (uB i)

@[expose] def zOf (e : ℕ × ℕ × ℕ × ℕ) : List (Fin 2 × Bool) := zword e.2.1 e.2.2.1 e.2.2.2


@[expose] def zGen (j : ℕ) : List (Fin 2 × Bool) := if j = 0 then zOne else zTwo


end CFSG.ComponentClassification.GrSLit.L34Facts.Real
