module

public import CFSG.LocalAnalysis.ComponentClassification.J2CoverModelsRigid

public section

namespace CFSG.ComponentClassification.J2Cover

open Models


theorem ctss_j2_involutions :
    (∀ x : P, orderOf x = 2 → fixCount (x : Perm315) = 11 ∨ fixCount (x : Perm315) = 15) ∧
    (∀ x y : P, orderOf x = 2 → orderOf y = 2 →
      fixCount (x : Perm315) = fixCount (y : Perm315) → ∃ g : P, g * x * g⁻¹ = y) ∧
    (∀ s : S, orderOf s = 2 → (fixCount (s : Perm315) = 11 ∧ fCoc s s = 0) ∨
      (fixCount (s : Perm315) = 15 ∧ fCoc s s = 1)) ∧
    orderOf (elt 4) = 2 ∧ fixCount (elt 4 : Perm315) = 11 ∧ orderOf (elt 2) = 2 ∧
      fixCount (elt 2 : Perm315) = 15 :=
  ⟨involution_fixCount, fun _ _ hx hy h => involution_conj hx hy h, fCoc_diag, orderOf_elt_four,
    fixCount_elt_four, orderOf_elt_two, fixCount_elt_two⟩


end CFSG.ComponentClassification.J2Cover
