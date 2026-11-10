module

public import CFSG.Quasithin.Background.HMathieuBits
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.ASVolI.AppH

open CFSG.Quasithin.H.Mathieu


structure KData where
  n : ℕ
  cols : List (List ℕ)
  lu : ℕ
  dU : ℕ
  xm : ℕ
  xb : List (ℕ × ℕ)

namespace KData


end KData

end CFSG.ASVolI.AppH
