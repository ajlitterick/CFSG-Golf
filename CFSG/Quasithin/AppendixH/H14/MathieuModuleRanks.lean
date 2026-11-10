module

public import CFSG.Quasithin.AppendixH.H14.MathieuStabilizerClasses
public import CFSG.Quasithin.AppendixH.H14.AutM22InvolutionClasses
public import CFSG.Quasithin.AppendixH.H14.SectionRankEngine
public import CFSG.Quasithin.AppendixH.H14.MathieuModuleCoordinates

public section

namespace CFSG.Quasithin.AppendixH.H14

open CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Monster.Code CFSG.ASVolI.ChH


@[expose] def actSec11 (isCode : Bool) : Array ℕ → ℕ → ℕ :=
  if isCode then actC11 else act11

@[expose] def actSec10 (isCode : Bool) : Array ℕ → ℕ → ℕ :=
  if isCode then actC10 else act10


section Certs


end Certs

end CFSG.Quasithin.AppendixH.H14
