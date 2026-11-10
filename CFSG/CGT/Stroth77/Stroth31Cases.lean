module

public import CFSG.CGT.Stroth77.Stroth31Proof

public section

namespace CFSG.CGT.Stroth77

open scoped commutatorElement

variable {G : Type*} [Group G] [Finite G]

@[expose] noncomputable def strothCab {D : Subgroup G} {τ : StrothTypeIndex}
    (dD : StrothWeakTypeData D τ) : G :=
  (dD.c : G) * (dD.a : G) * (dD.b : G)

@[expose] noncomputable def strothAB {D : Subgroup G} {τ : StrothTypeIndex}
    (dD : StrothWeakTypeData D τ) : G :=
  (dD.a : G) * (dD.b : G)

@[simp] theorem strothCab_def {D : Subgroup G} {τ : StrothTypeIndex}
    (dD : StrothWeakTypeData D τ) :
    strothCab dD = (dD.c : G) * (dD.a : G) * (dD.b : G) := rfl

@[simp] theorem strothAB_def {D : Subgroup G} {τ : StrothTypeIndex}
    (dD : StrothWeakTypeData D τ) :
    strothAB dD = (dD.a : G) * (dD.b : G) := rfl

@[expose] def strothConj (r x : G) : G := r⁻¹ * x * r

@[simp] theorem strothConj_def (r x : G) : strothConj r x = r⁻¹ * x * r := rfl


end CFSG.CGT.Stroth77
