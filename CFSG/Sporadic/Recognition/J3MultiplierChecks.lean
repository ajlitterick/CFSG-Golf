module

public import CFSG.Monster.Schur.CentralEps
public import CFSG.Sporadic.Recognition.J3MultiplierWords
public import CFSG.Sporadic.Recognition.CoverRecipe

public section

namespace CFSG.Sporadic.Recognition.J3Multiplier

open CFSG.CosetTable CFSG.Monster.Schur CFSG.Sporadic.Recognition.CoverRecipe


@[expose] def plainWords : List (List (Fin 2 × Bool)) := U ++ (List.finRange 2).map T


end CFSG.Sporadic.Recognition.J3Multiplier
