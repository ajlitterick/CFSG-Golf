module

public import CFSG.Monster.B.Dyadic.Defs
public import CFSG.Certificates.Kernel.BabyMonster.PktSound
public import CFSG.Certificates.Kernel.BabyMonster.Dyadic.Gens

public section

namespace CFSG.Monster.B.Dyadic

@[expose] def MqN (N : ℕ → ℕ → ℤ) : Matrix (Fin 4371) (Fin 4371) ℚ := fun t u => (N t u : ℚ) / 8


@[expose] noncomputable def numer26 (t u : ℕ) : ℤ :=
  CFSG.KC.BM.Pkt.kNumMono (CFSG.KC.BM.nthN CFSG.KC.BM.Dyadic.G26.b0 0) t u

@[expose] noncomputable def Mq26 : Matrix (Fin 4371) (Fin 4371) ℚ := MqN numer26

end CFSG.Monster.B.Dyadic

end
