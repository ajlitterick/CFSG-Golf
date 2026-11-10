
module

public import CFSG.Sporadic.ThSchreier.CoreHyperplaneBase

public import CFSG.Sporadic.ThSchreier.Max3AutBase1
public meta import CFSG.Sporadic.ThSchreier.Rigidity

@[expose] public section

namespace CFSG.Sporadic.ThSchreier

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Max3 CFSG.Certificates Matrix

theorem nf_eq_mul
    (s : ZMod 2) (v : Fin 8 → ZMod 2) : nf s v = z ^ s.val * nf 0 v := by
  simp only [nf, ZMod.val_zero, pow_zero, one_mul]

end CFSG.Sporadic.ThSchreier
