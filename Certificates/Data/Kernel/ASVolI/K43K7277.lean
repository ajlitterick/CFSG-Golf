module

public import Certificates.Data.Kernel.ASVolI.K43K
public import Certificates.Data.Kernel.HMathieu.Bfs
public import CFSG.Mathlib.Decide.Nodup

public section

namespace CFSG.KS.ASVolI

open CFSG.ASVolI.K43Data CFSG.KC.HMathieu CFSG.KC.Enum CFSG.KS CFSG.KS.MathieuAut
  CFSG.Quasithin.H.Mathieu CFSG.Monster.Code


@[expose] def moColsK : List (List ℕ) := moGens.map fun a => colsC11 a.toList

@[expose] def applyWordK (w : List ℕ) (m : ℕ) : ℕ :=
  w.foldr (fun g acc => actM (moColsK.getD g []) acc) m

@[expose] def indep6B (cands : List ℕ) : Bool :=
  let bs := pick6 cands
  bs.length == 6 && CFSG.Decide.bitsetNodup (combos bs)

@[expose] def f4Pred (m : ℕ) : Bool :=
  (w5Masks ()).contains m || indep6B ((wordPool 10 2).map fun w => applyWordK w m)

@[expose] def f4Slice (i : ℕ) : Bool := (List.range' (64 * i) 64).all f4Pred


end CFSG.KS.ASVolI

end
