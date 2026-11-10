module

public import CFSG.Certificates.Kernel.Th.S.BigS
public import CFSG.Certificates.Kernel.Th.S.Data.Sm_const
public import CFSG.Certificates.Kernel.Th.S.Data.Seed_const
public import CFSG.Certificates.Kernel.Th.S.Data.M3_const
public import Certificates.Data.Kernel.LceSSeg
public import CFSG.Certificates.Kernel.Bounds.Core3
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.RowsUnfold

public section

set_option maxRecDepth 100000

#kc_repo #kc_items_root CFSG.KD.ThM3.Rows_M3_R.f6P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/M3_R_6_P.bin" 44 8702089246535798533
#kc_repo #kc_items_root CFSG.KD.ThM3.Rows_M3_R.f6I "CFSG/Certificates/Kernel/Th/Checks2/data/rows/M3_R_6_I.bin" 15 5512800217539681965
#kc_repo #kc_items_root CFSG.KD.ThM3.Rows_M3_R.f14P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/M3_R_14_P.bin" 329 3041409730081082928
#kc_repo #kc_items_root CFSG.KD.ThM3.Rows_M3_R.f14I "CFSG/Certificates/Kernel/Th/Checks2/data/rows/M3_R_14_I.bin" 39 18362343629704035864
#kc_repo #kc_items_root CFSG.KD.ThM3.Rows_M3_R.f17P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/M3_R_17_P.bin" 7956 17412235879230179726
#kc_repo #kc_items_root CFSG.KD.ThM3.Rows_M3_R.f17I "CFSG/Certificates/Kernel/Th/Checks2/data/rows/M3_R_17_I.bin" 2806 3057087102027320484
#kc_repo #kc_items_root CFSG.KD.ThM3.Rows_M3_R.f18P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/M3_R_18_P.bin" 251 12125586827065694877
#kc_repo #kc_items_root CFSG.KD.ThM3.Rows_M3_R.f18I "CFSG/Certificates/Kernel/Th/Checks2/data/rows/M3_R_18_I.bin" 35 3525205344064885652

namespace CFSG.KD.ThM3.Rows_M3_R

@[expose] noncomputable def f6 (g : Nat) : Bool :=
  Nat.beq (CFSG.KD.ThM3.RB (CFSG.KD.ThM3.Rows_M3_R.f6P (3 * g + 0))) (CFSG.KC.Th.mulB CFSG.KD.ThS.c
    CFSG.KD.ThS.rm (CFSG.KD.ThM3.RB (CFSG.KD.ThM3.Rows_M3_R.f6P (3 * g + 1))) (CFSG.KD.ThM3.RB
    (CFSG.KD.ThM3.Rows_M3_R.f6P (3 * g + 2))))

@[expose] noncomputable def f14 (g : Nat) : Bool :=
  Nat.beq (CFSG.KD.ThM3.RB (CFSG.KD.ThM3.Rows_M3_R.f14P (8 * g + 0))) (CFSG.KC.Th.BigS.powB
    CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThS.ONE (CFSG.KC.Th.BigS.wordAB CFSG.KD.ThS.c
    CFSG.KD.ThS.rm CFSG.KD.ThS.ONE (CFSG.KD.ThM3.RB (CFSG.KD.ThM3.Rows_M3_R.f14P (8 * g + 1)))
    (CFSG.KD.ThM3.RB (CFSG.KD.ThM3.Rows_M3_R.f14P (8 * g + 2))) (CFSG.KD.ThM3.RB
    (CFSG.KD.ThM3.Rows_M3_R.f14P (8 * g + 3))) (CFSG.KD.ThM3.Rows_M3_R.f14P (8 * g + 4))
    (CFSG.KD.ThM3.Rows_M3_R.f14P (8 * g + 5))) (CFSG.KD.ThM3.Rows_M3_R.f14P (8 * g + 6))
    (CFSG.KD.ThM3.Rows_M3_R.f14P (8 * g + 7)))

@[expose] noncomputable def f17 (g : Nat) : Bool :=
  Nat.beq (CFSG.KD.ThM3.RB (CFSG.KD.ThM3.Rows_M3_R.f17P (3 * g + 0))) (CFSG.KC.Th.mulB CFSG.KD.ThS.c
    CFSG.KD.ThS.rm (CFSG.KD.ThM3.RB (CFSG.KD.ThM3.Rows_M3_R.f17P (3 * g + 1))) (CFSG.KD.ThM3.RB
    (CFSG.KD.ThM3.Rows_M3_R.f17P (3 * g + 2))))

@[expose] noncomputable def f18 (g : Nat) : Bool :=
  Nat.beq (CFSG.KD.ThM3.RB (CFSG.KD.ThM3.Rows_M3_R.f18P (6 * g + 0))) (CFSG.KC.Th.BigS.wordAB
    CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThS.ONE (CFSG.KD.ThM3.RB (CFSG.KD.ThM3.Rows_M3_R.f18P (6 *
    g + 1))) (CFSG.KD.ThM3.RB (CFSG.KD.ThM3.Rows_M3_R.f18P (6 * g + 2))) (CFSG.KD.ThM3.RB
    (CFSG.KD.ThM3.Rows_M3_R.f18P (6 * g + 3))) (CFSG.KD.ThM3.Rows_M3_R.f18P (6 * g + 4))
    (CFSG.KD.ThM3.Rows_M3_R.f18P (6 * g + 5)))

end CFSG.KD.ThM3.Rows_M3_R

#kc_rows_unfold CFSG.KD.ThM3.Rows_M3_R.f6 3 as CFSG.KD.ThM3.rS names CFSG.KD.ThM3.Rows_M3_R.f6I eval
  CFSG.KD.ThM3.Rows_M3_R.f6P
#kc_rows_unfold CFSG.KD.ThM3.Rows_M3_R.f14 8 as CFSG.KD.ThM3.rQ names CFSG.KD.ThM3.Rows_M3_R.f14I
  eval CFSG.KD.ThM3.Rows_M3_R.f14P
#kc_rows_unfold CFSG.KD.ThM3.Rows_M3_R.f17 510 as CFSG.KD.ThM3.rNF names CFSG.KD.ThM3.Rows_M3_R.f17I
  eval CFSG.KD.ThM3.Rows_M3_R.f17P
#kc_rows_unfold CFSG.KD.ThM3.Rows_M3_R.f18 7 as CFSG.KD.ThM3.rC names CFSG.KD.ThM3.Rows_M3_R.f18I
  eval CFSG.KD.ThM3.Rows_M3_R.f18P


theorem CFSG.KD.ThM3.rU : Nat.beq (CFSG.KD.ThM3.RB (nat_lit 6)) (CFSG.KC.Th.mulB CFSG.KD.ThS.c
    CFSG.KD.ThS.rm (CFSG.KC.Th.BigS.powB CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThS.ONE
    (CFSG.KD.ThM3.RB (nat_lit 5)) (nat_lit 2) (nat_lit 2)) (CFSG.KD.ThM3.RB (nat_lit 4))) = true :=
    by
  quickRfl


theorem CFSG.KD.ThM3.rV : Nat.beq (CFSG.KD.ThM3.RB (nat_lit 12)) (CFSG.KC.Th.mulB CFSG.KD.ThS.c
    CFSG.KD.ThS.rm (CFSG.KC.Th.BigS.powB CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThS.ONE
    (CFSG.KD.ThM3.RB (nat_lit 11)) (nat_lit 18) (nat_lit 5)) (CFSG.KD.ThM3.RB (nat_lit 10))) = true
    := by
  quickRfl

theorem CFSG.KD.ThM3.rX : Nat.beq (CFSG.KD.ThM3.RB (nat_lit 13)) (CFSG.KC.Th.BigS.powB CFSG.KD.ThS.c
    CFSG.KD.ThS.rm CFSG.KD.ThS.ONE (CFSG.KD.ThM3.RB (nat_lit 12)) (nat_lit 14) (nat_lit 4)) = true
    := by
  quickRfl

theorem CFSG.KD.ThM3.rY : Nat.beq (CFSG.KD.ThM3.RB (nat_lit 14)) (CFSG.KC.Th.mulB CFSG.KD.ThS.c
    CFSG.KD.ThS.rm (CFSG.KD.ThM3.RB (nat_lit 4)) (CFSG.KC.Th.BigS.powB CFSG.KD.ThS.c CFSG.KD.ThS.rm
    CFSG.KD.ThS.ONE (CFSG.KD.ThM3.RB (nat_lit 6)) (nat_lit 9) (nat_lit 4))) = true := by
  quickRfl


theorem CFSG.KD.ThM3.rZ : Nat.beq (CFSG.KD.ThM3.RB (nat_lit 16)) (CFSG.KC.Th.BigS.powB CFSG.KD.ThS.c
    CFSG.KD.ThS.rm CFSG.KD.ThS.ONE (CFSG.KC.Th.BigS.wordAB CFSG.KD.ThS.c CFSG.KD.ThS.rm
    CFSG.KD.ThS.ONE (CFSG.KD.ThM3.RB (nat_lit 13)) (CFSG.KD.ThM3.RB (nat_lit 14)) (CFSG.KD.ThM3.RB
    (nat_lit 15)) (nat_lit 84) (nat_lit 4)) (nat_lit 9) (nat_lit 4)) = true := by
  quickRfl


theorem CFSG.KD.ThM3.rD : Nat.beq (CFSG.KD.ThM3.RB (nat_lit 547)) (CFSG.KC.Th.BigS.wordAB
    CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThS.ONE (CFSG.KD.ThM3.RB (nat_lit 13)) (CFSG.KD.ThM3.RB
    (nat_lit 14)) (CFSG.KD.ThM3.RB (nat_lit 15)) (nat_lit 5986089550763093) (nat_lit 27)) = true :=
    by
  quickRfl


end
