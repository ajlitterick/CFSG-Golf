module

public import CFSG.ClassicalInvolution.SmallCases.NDBE7S
public import CFSG.ClassicalInvolution.SmallCases.NDBG10

public section

namespace CFSG.ClassicalInvolution.NDB

variable {p f : ℕ} [Fact p.Prime]

variable (p f) in
theorem exoticFrameSpin_of (hres : SpinOuterKleinAlpha p) : ExoticFrameSpin p f := by
  intro G _ _ _ K z hS hnoT hnoF D i hi
  exact Exotic.spinFrame_exists hres hS hnoT hnoF D i hi

end CFSG.ClassicalInvolution.NDB
