module

public import CFSG.Quasithin.Vol2.Ch7Stmt326Lt
public import CFSG.Quasithin.Vol2.Ch10T326CBridge

public section

namespace CFSG.Quasithin.H13

open scoped IsMulCommutative


theorem stmt3_2_6Lt_of_C (h326 : Stmt3_2_6C) : Stmt3_2_6Lt :=
  fun G _ _ T L I hfsu hlt => (Vol2.Ch10.tmpL6_3_2_6C_of_stmt3_2_6C h326 G T L I hfsu hlt).2.2

end CFSG.Quasithin.H13
