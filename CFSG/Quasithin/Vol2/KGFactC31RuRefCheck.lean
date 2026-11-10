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
@[expose] def b16A : List (Array ℕ) := wsA basis16W
@[expose] def b32A : List (Array ℕ) := wsA basis32W
@[expose] def bV32EA : List (Array ℕ) := wsA basisV32EW

@[expose] def spE : List (Array ℕ) := spanA bEA
@[expose] def sp64 : List (Array ℕ) := spanA b64A
@[expose] def sp3 : List (Array ℕ) := spanA b3A
@[expose] def sp16 : List (Array ℕ) := spanA b16A
@[expose] def sp32 : List (Array ℕ) := spanA b32A
@[expose] def spV32E : List (Array ℕ) := spanA bV32EA

@[expose] def xEA : Array ℕ := wA xEW
@[expose] def x16A : Array ℕ := wA x16W
@[expose] def x32A : Array ℕ := wA x32W

@[expose] def pA : ℕ → Array ℕ → Array ℕ
  | 0, _ => idA 4060
  | k + 1, t => compA 4060 t (pA k t)


@[expose] def normsA (t ti : Array ℕ) (bs sp : List (Array ℕ)) : Bool :=
  bs.all fun b => inA sp (cjA t ti b)

@[expose] def centA (bs : List (Array ℕ)) (c : Array ℕ) : Bool := bs.all fun b => commA c b


@[expose] def conjSp64 : List (List (Array ℕ)) :=
  conj64W.map fun w => spanA (b64A.map (cjA (wA w) (ruInv (wA w))))


@[expose] def commutA (a b : Array ℕ) : Array ℕ :=
  compA 4060 (compA 4060 (compA 4060 a b) (ruInv a)) (ruInv b)


end CFSG.Quasithin.KGC31.Ru

end
