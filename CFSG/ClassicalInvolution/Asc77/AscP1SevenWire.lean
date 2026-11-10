module

public import CFSG.ClassicalInvolution.Asc77.AscP1SevenCubeKey
public import CFSG.ClassicalInvolution.Asc77.AscP1SevenStar
public import CFSG.ClassicalInvolution.Asc77.AscP1ThompsonTwelve
public import CFSG.ClassicalInvolution.AschTight.Sec7KeyD

public section

namespace CFSG.ClassicalInvolution.Asc77

variable {p f : ℕ} [Fact p.Prime]

theorem thompsonKey : ThompsonKey p f :=
  CFSG.ClassicalInvolution.Disconnected.AschTight.Sec7.l7_1Key p f

theorem thompsonCube : ThompsonCube p f := thompsonCube_of_key thompsonKey

theorem thompsonStar : ThompsonStar p f := thompsonStar_of_key thompsonKey


end CFSG.ClassicalInvolution.Asc77
