module

public import CFSG.GH74.Generic.Front.S2
public import CFSG.GH74.Generic.Front.OuterThree
public import CFSG.GH74.Generic.Front.DataStatement
public import CFSG.GH74.Generic.Front.SpOuter

public section

namespace CFSG.GH74.Generic

open CFSG CFSG.GH74 CFSG.Blueprint

theorem s2_shapeCase_proved : S_shapeCase @ShapeS2 :=
  s2_shapeCase frontDataStatement (outerStatement_of_three outerThreeStatement) spOuterInvolution


end CFSG.GH74.Generic
