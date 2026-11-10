module

public import Certificates.Data.CFSGNative.ExcCensus.Check

public section

namespace CFSG.StandardType.GGQ2Frame.ExcRaw.Chk

set_option compiler.extract_closed false

structure ICSearch where
  S : Search
  common : Nat → Nat → Option (Nat × Nat × List Nat × Array (Array Int) × CommonW)
  deriving Inhabited

@[expose] def bodyIC (T : Tabs) (m : Fin 6) (X : ICSearch) (cv cy : Nat) : Bool :=
  let d := dim m
  match X.common cv cy with
  | some (a, b, rows, B, W) =>
    decide (a < 3) && (b == 1 || b == 2) && candOK T m cv (combN d cv cy a b) rows B &&
      commonOK T m cv (combN d cv cy a b) (T.zm[cv]!) (T.zm[combN d cv cy a b]!) W
  | none => false


end CFSG.StandardType.GGQ2Frame.ExcRaw.Chk

end
