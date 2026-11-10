module

public import CFSG.Quasithin.Background.H156K
public import CFSG.Quasithin.Background.H156Gen

public section

namespace CFSG.Quasithin.H156

open CFSG.Quasithin.H158U CFSG.Quasithin.H158T CFSG.Quasithin.H.Coc24 CFSG.Quasithin.H.Mathieu
  CFSG.Quasithin.H.ModChk CFSG.Quasithin.H.LU CFSG.Monster.Code CFSG.Quasithin CFSG.Open
  CFSG.Quasithin.H.ZTrans CFSG.Quasithin.H.Coc

@[expose] def c2 : List ℕ := [1, 2, 0, 1, 1, 3, 3, 0, 3, 1, 2]

@[expose] def c3 : List ℕ := [0, 0, 0, 0, 0, 1, 0, 2, 1, 0, 4]

@[expose] def c6 : List ℕ := [0, 0, 27, 48, 16, 27, 35, 3, 63, 37, 40]


@[expose] def beta2 : W11 →* Wn 2 := maskHom 11 2 c2


@[expose] def V9 : Subgroup W11 := beta2.ker


@[expose] noncomputable def gT3 : MulAut W11 := rhoM24 ⟨t3P, t3_mem⟩

@[expose] noncomputable def gT2 : MulAut W11 := rhoM24 ⟨t2P, t2_mem⟩


end CFSG.Quasithin.H156
