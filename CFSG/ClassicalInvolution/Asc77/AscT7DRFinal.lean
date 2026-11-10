module

public import CFSG.ClassicalInvolution.Asc77.AscT7C2RFive
public import CFSG.ClassicalInvolution.Asc77.AscT7C2RChain
public import CFSG.ClassicalInvolution.Asc77.AscT7DRFive
public import CFSG.ClassicalInvolution.Asc77.AscT7DRLit
public import CFSG.ClassicalInvolution.Asc77.AscT7BExit22S
public import CFSG.ClassicalInvolution.Asc77.AscT7BFinal23
public import CFSG.ClassicalInvolution.Asc77.AscT7ED2
public import CFSG.ClassicalInvolution.Asc77.AscT7EExit24
public import CFSG.ClassicalInvolution.Asc77.AscT7FF
public import CFSG.ClassicalInvolution.Asc77.AscT7FI
public import CFSG.ClassicalInvolution.RouteD.G2D4G2NonToralFive
public import CFSG.ClassicalInvolution.RouteD.TypeTwistedDDischarge

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

variable {p f : ℕ} [Fact p.Prime]

theorem c24_1_of_core (hcore : C24_9_core p f) (hbig : C24_8_big p f) (hpair : C24_pair p f) :
    C24_1 p f :=
  c24_1_of_inputs'' (T7C2.c24_8_of_big (T7C2.c24_9_of_core hcore) hbig)
    (T7C2.c24_9_of_core hcore) (c24_chain_of_pair hpair)

theorem c25_E4_of_exits (h19 : C25_19 p f) (h21 : C25_21 p f) : C25_E4 p f :=
  c25_E4_of_steps (c25_setup_of c25_RS_proved) h19 h21

theorem c25_E4_of_sylow (h2 : C25_2_t p f) (h17 : C25_17_idx p f) (h20 : C25_20 p f) :
    C25_E4 p f :=
  c25_E4_of_exits (c25_19_of_sylow p f h2 h17) (c25_21_of_sylow p f h20)


end CFSG.ClassicalInvolution.Asc77
