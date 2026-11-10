module

public import CFSG.ClassicalInvolution.RouteD.ExoticSingleClique
public import CFSG.ClassicalInvolution.RouteD.ExoticSingleMinus

public section

namespace CFSG.ClassicalInvolution.RouteD.Exotic

open CFSG.ClassicalInvolution.Generic.CoreAssembly

variable {p f : ℕ} [Fact p.Prime]

theorem rowSingleOrth_of_small (hOdd : RowPiece p f ShapeSingleOddSmall)
    (hMinus : RowPiece p f ShapeSingleMinusSmall) : RowPiece p f ShapeSingleOrth :=
  rowSingleOrth_of_parts rowSingleOddLarge hOdd rowSinglePlusLarge rowSinglePlusSmall
    rowSingleMinusLarge hMinus

theorem rowSingleOrth : RowPiece p f ShapeSingleOrth :=
  rowSingleOrth_of_small rowSingleOddSmall rowSingleMinusSmall

end CFSG.ClassicalInvolution.RouteD.Exotic
