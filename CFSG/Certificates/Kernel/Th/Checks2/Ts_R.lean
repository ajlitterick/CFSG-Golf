
module

public import CFSG.Certificates.Kernel.Th.S.BigS
public import CFSG.Certificates.Kernel.Th.S.DceS
public import CFSG.Certificates.Kernel.Th.S.TsS
public import CFSG.Certificates.Kernel.Th.S.Data.Sm_const
public import CFSG.Certificates.Kernel.Th.S.Data.Seed_const
public import CFSG.Certificates.Kernel.Th.S.Data.M3_const
public import CFSG.Certificates.Kernel.Th.S.Data.Ts_const
public import Certificates.Data.Kernel.LceSSeg
public import CFSG.Certificates.Kernel.Bounds.Core3
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.RowsUnfold

public section

set_option maxRecDepth 100000

#kc_repo #kc_items_root CFSG.KD.ThTs.Rows_Ts_R.f2P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Ts_R_2_P.bin" 47 4316860503771176349
#kc_repo #kc_items_root CFSG.KD.ThTs.Rows_Ts_R.f14P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Ts_R_14_P.bin" 80 16108787186530764132
#kc_repo #kc_items_root CFSG.KD.ThTs.Rows_Ts_R.f14I "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Ts_R_14_I.bin" 40 348359025702806052

namespace CFSG.KD.ThTs.Rows_Ts_R

@[expose] noncomputable def f2 (g : Nat) : Bool :=
  Nat.beq (CFSG.KD.ThTs.RB (CFSG.KD.ThTs.Rows_Ts_R.f2P (4 * g + 0))) (CFSG.KC.Th.BigS.wordAB
    CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThS.ONE CFSG.KD.ThSeed.SA CFSG.KD.ThSeed.SB
    (CFSG.KD.ThTs.RB (CFSG.KD.ThTs.Rows_Ts_R.f2P (4 * g + 1))) (CFSG.KD.ThTs.Rows_Ts_R.f2P (4 * g +
    2)) (CFSG.KD.ThTs.Rows_Ts_R.f2P (4 * g + 3)))

@[expose] noncomputable def f14 (g : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KD.ThTs.RB
    (CFSG.KD.ThTs.Rows_Ts_R.f14P (2 * g + 0))) (CFSG.KD.ThTs.RB (CFSG.KD.ThTs.Rows_Ts_R.f14P (2 * g
    + 1)))) CFSG.KD.ThS.ONE

end CFSG.KD.ThTs.Rows_Ts_R

#kc_unfold CFSG.KD.ThTs.rLY CFSG.KD.ThTs.Rows_Ts_R.f2 0 eval CFSG.KD.ThTs.Rows_Ts_R.f2P
#kc_rows_unfold CFSG.KD.ThTs.Rows_Ts_R.f14 8 as CFSG.KD.ThTs.rIE names CFSG.KD.ThTs.Rows_Ts_R.f14I
  eval CFSG.KD.ThTs.Rows_Ts_R.f14P


theorem CFSG.KD.ThTs.rK : Nat.beq (CFSG.KD.ThTs.RB (nat_lit 6)) (CFSG.KC.Th.BigS.wordAB
    CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThS.ONE (CFSG.KD.ThTs.RB (nat_lit 1)) (CFSG.KD.ThTs.RB
    (nat_lit 2)) (CFSG.KD.ThTs.RB (nat_lit 3)) (nat_lit 69) (nat_lit 4)) = true := by
  quickRfl


theorem CFSG.KD.ThTs.rE6 : Nat.beq (CFSG.KD.ThTs.RB (nat_lit 14)) (CFSG.KC.Th.mulB CFSG.KD.ThS.c
    CFSG.KD.ThS.rm (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KC.Th.mulB CFSG.KD.ThS.c
    CFSG.KD.ThS.rm (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KC.Th.mulB CFSG.KD.ThS.c
    CFSG.KD.ThS.rm (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KC.Th.mulB CFSG.KD.ThS.c
    CFSG.KD.ThS.rm (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KC.Th.mulB CFSG.KD.ThS.c
    CFSG.KD.ThS.rm (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KC.Th.mulB CFSG.KD.ThS.c
    CFSG.KD.ThS.rm (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KD.ThTs.RB (nat_lit 13))
    (CFSG.KD.ThTs.RB (nat_lit 11))) (CFSG.KD.ThTs.RB (nat_lit 13))) (CFSG.KD.ThTs.RB (nat_lit 11)))
    (CFSG.KD.ThTs.RB (nat_lit 13))) (CFSG.KD.ThTs.RB (nat_lit 11))) (CFSG.KD.ThTs.RB (nat_lit 13)))
    (CFSG.KD.ThTs.RB (nat_lit 11))) (CFSG.KD.ThTs.RB (nat_lit 13))) (CFSG.KD.ThTs.RB (nat_lit 11)))
    (CFSG.KD.ThTs.RB (nat_lit 13))) (CFSG.KD.ThTs.RB (nat_lit 11))) (CFSG.KD.ThTs.RB (nat_lit 13)))
    = true := by
  quickRfl


theorem CFSG.KD.ThTs.rV : Nat.beq (CFSG.KD.ThTs.RB (nat_lit 26)) (CFSG.KC.Th.BigS.wordAB
    CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThS.ONE CFSG.KD.ThSeed.SA CFSG.KD.ThSeed.SB
    (CFSG.KD.ThTs.RB (nat_lit 0)) (nat_lit 373911662824283980869) (nat_lit 35)) = true := by
  quickRfl


end
