module

public import CFSG.Quasithin.Vol2.KGFactC31RuRefData
public import CFSG.Quasithin.Vol2.KGFactC31RuData
public import CFSG.Sporadic.Schreier.RuCheckCentersInputs

public section

namespace CFSG.Quasithin.KGC31.Ru

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.RuSchreier

@[expose] def wsA (ws : List (List ℤ)) : List (Array ℕ) := ws.map wA

@[expose] def bEA : List (Array ℕ) := wsA basisEW
@[expose] def b64A : List (Array ℕ) := wsA basis64W
@[expose] def b3A : List (Array ℕ) := wsA basis3W
@[expose] def bV32EA : List (Array ℕ) := wsA basisV32EW

@[expose] def spE : List (Array ℕ) := spanA bEA
@[expose] def sp64 : List (Array ℕ) := spanA b64A
@[expose] def spV32E : List (Array ℕ) := spanA bV32EA

@[expose] def xEA : Array ℕ := wA xEW

@[expose] def pA : ℕ → Array ℕ → Array ℕ
  | 0, _ => idA 4060
  | k + 1, t => compA 4060 t (pA k t)


@[expose] def normsA (t ti : Array ℕ) (bs sp : List (Array ℕ)) : Bool :=
  bs.all fun b => inA sp (cjA t ti b)

@[expose] def centA (bs : List (Array ℕ)) (c : Array ℕ) : Bool := bs.all fun b => commA c b


@[expose] def commutA (a b : Array ℕ) : Array ℕ :=
  compA 4060 (compA 4060 (compA 4060 a b) (ruInv a)) (ruInv b)


end CFSG.Quasithin.KGC31.Ru

end
