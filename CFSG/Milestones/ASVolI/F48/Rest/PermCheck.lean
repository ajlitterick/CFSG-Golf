module

public import CFSG.Sporadic.HNOddCore.ChainUtil
public import CFSG.Sporadic.HNOddCore.OrbitCert

public section

namespace CFSG.ASVolI

open CFSG.ONSchreier.Native

section Words

variable {n : ℕ}

@[expose] def burnsideF48t_letA (L Li : Array (Array ℕ)) (l : Fin n × Bool) : Array ℕ :=
  if l.2 then L[(l.1 : ℕ)]! else Li[(l.1 : ℕ)]!

@[expose] def burnsideF48t_evA (N : ℕ) (L Li : Array (Array ℕ)) : List (Fin n × Bool) → Array ℕ
  | [] => pid N
  | l :: w => pcomp N (burnsideF48t_letA L Li l) (burnsideF48t_evA N L Li w)

end Words


section Checks

open CFSG.Sporadic.HNOddCore CFSG.Monster.B.Co2.Native CFSG.Certificates.Native


end Checks

end CFSG.ASVolI
