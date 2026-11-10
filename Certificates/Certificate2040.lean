module

public import CFSG.LocalAnalysis.ComponentClassification.WittDesignHyperovals
public import CFSG.LocalAnalysis.ComponentClassification.WittDesignPlaneUnique
public meta import CFSG.LocalAnalysis.ComponentClassification.WittDesignHyperovals

public section

open CFSG.ComponentClassification.WittDesign

namespace Certificates

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.WittDesign in
open CFSG.Monster.B.Classical.Plane in
theorem certificate2040 : ∀ x, deltaPerm (deltaPerm (deltaPerm x)) = x :=
  by
    intro x
    fin_cases x <;> rfl

end Certificates
