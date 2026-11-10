module

public import CFSG.ClassicalInvolution.RouteD.TWEB6Main
public import CFSG.ClassicalInvolution.RouteD.TWS6D4Rank
public import CFSG.ClassicalInvolution.RouteD.TWS6SRow

public section

namespace CFSG.ClassicalInvolution.RouteD.TwinY

variable (p f : ℕ) [Fact p.Prime]

structure TwinVisNCOpen : Prop where
  visB3 : TwinYVisibleOn p f fun t n => t = .POmegaOdd ∧ n = 3
  ncB3 : TwinYNoCentralOn p f fun t n => t = .POmegaOdd ∧ n = 3
  visTD4 : TwinYVisibleOn p f fun t n => t = .POmegaMinus ∧ n = 4
  ncTD4 : TwinYNoCentralOn p f fun t n => t = .POmegaMinus ∧ n = 4

end CFSG.ClassicalInvolution.RouteD.TwinY
