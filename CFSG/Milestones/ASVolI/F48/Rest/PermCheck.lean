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

@[expose] def burnsideF48t_baseArr {N : ℕ} (b : List (Fin N)) : Array ℕ := (b.map Fin.val).toArray

@[expose] def burnsideF48t_levels (N : ℕ) (O : Array (Array ℕ)) (W : Array (List ℤ))
    (b : List (Fin N)) : Array Level :=
  rawLevels N (strongArrs N O W) (burnsideF48t_baseArr b)

@[expose] def burnsideF48t_sift (N : ℕ) (lv : Array Level) (b : List (Fin N)) (t : Array ℕ) : Bool :=
  siftA N lv (burnsideF48t_baseArr b) 0 t


@[expose] def burnsideF48t_closedL (N : ℕ) (gs : Array (Array ℕ)) (E : List (Array ℕ)) : Bool :=
  E.contains (pid N) && E.all fun e => gs.all fun g => E.contains (pcomp N e g)

end Checks

end CFSG.ASVolI
