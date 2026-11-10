module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.IntrThm33a

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

variable {G : Type*} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {θ : G → Subgroup G}
  {Y X : Subgroup G}

namespace Thm33a

omit [Finite G] in
theorem nearAsolvAction_of_mem_mtil (hθ : NearFunctor p A θ) (hX : X ∈ mtil p A θ) :
    NearAsolvAction p A X where
  prime := hθ.prime
  odd := hθ.odd
  elemAbelian := hθ.elemAbelian
  admits := hX.1.1
  nearPSolvable := hX.1.2.2.2.1
  solvable_cen := hX.1.2.2.2.2


end Thm33a


end CFSG.SignalizerFunctorTheorem.McBride.Near
