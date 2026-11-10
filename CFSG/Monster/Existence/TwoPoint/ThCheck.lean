module

public import CFSG.Monster.Existence.TwoPoint.HNRigid
public import CFSG.Monster.Existence.TwoPoint.ThData

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.Griess CFSG.Monster.Generated
  CFSG.Monster.B.Short

@[expose] def thLetterW (l : ℕ × Bool) : List Native.Gen :=
  if l.2 then thWU[l.1]! else thWV[l.1]!

@[expose] def thRelW (R : List (ℕ × Bool)) : List Native.Gen :=
  (R.reverse.map thLetterW).flatten


@[expose] def thNotTau : Native.Gen → Bool
  | .tau => false
  | _ => true

theorem thNotTau_spec {g : Native.Gen} (h : thNotTau g = true) : ¬ g = .tau := by
  cases g <;> simp_all [thNotTau]


@[expose] def thWAB : List Native.Gen := thWBeta ++ thWAlpha

@[expose] def thWAB3 : List Native.Gen := thWAB ++ thWAB ++ thWAB


@[expose] def thWS7 : List Native.Gen :=
  thWU[5]! ++ thWU[5]! ++ thWU[5]! ++ thWU[5]! ++ thWU[5]! ++ thWU[5]! ++ thWU[5]!


end CFSG.Monster.Existence
