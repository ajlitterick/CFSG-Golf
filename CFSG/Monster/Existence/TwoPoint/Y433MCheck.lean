module

public import CFSG.Monster.Existence.TwoPoint.Fi23S4Check

public section

namespace CFSG.Monster.Existence

open CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.Griess CFSG.Monster.Generated
  CFSG.Monster.B.Short

@[expose] def y433Sigma (c : ℕ) : ℕ := [3, 4, 5, 6, 9, 2, 1, 0, 7, 8].getD c 0

@[expose] def y433W (c : ℕ) : List Native.Gen :=
  if c = 10 then s4WGamma else fiWU[y433Sigma c]!


theorem y433Sigma_lt {c : ℕ} (hc : c < 10) : y433Sigma c < 10 := by
  have : ∀ c < 10, y433Sigma c < 10 := by decide
  exact this c hc


@[expose] def y433RelW (R : List ℕ) : List Native.Gen := (R.reverse.map y433W).flatten


@[expose] def y433SpiderR : List ℕ := (List.replicate 10 [0, 1, 2, 0, 5, 6, 0, 8, 9]).flatten

@[expose] def y433F213R : List ℕ := (List.replicate 9 [0, 5, 6, 7, 1, 2, 8]).flatten

@[expose] def y433F312R : List ℕ := (List.replicate 9 [0, 8, 9, 10, 1, 2, 5]).flatten


end CFSG.Monster.Existence
