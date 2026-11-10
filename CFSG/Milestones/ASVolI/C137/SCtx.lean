module

public import CFSG.Milestones.ASVolI.C137.SOff
public import CFSG.Milestones.ASVolI.C137.SFin
public import CFSG.Quasithin.H13.GoldschmidtC137L32Off

public section

namespace CFSG.ASVolI

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint CFSG.ASVolI.ChC
open CFSG.Quasithin.L3 CFSG.Quasithin.H13.U3 CFSG.Quasithin.H13.U3.GC137
open scoped commutatorElement

variable {G : Type} [Group G]

structure burnsideC137_SCtx (X T L P U : Subgroup G) (α : ↥L →* Γ) (U₁ U₂ : Subgroup G)
    (β₁ : ↥U₁ →* Multiplicative Vec) (β₂ : ↥U₂ →* Multiplicative Vec) : Prop where
  hT : IsSylowTwoOf T X
  hprod : ∀ x ∈ X, ∃ l ∈ L, ∃ t ∈ T, x = l * t
  hL : L ∈ cComp X
  lie : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 3 2 1
  hTP : T ≤ P
  hPX : P < X
  hmax : ∀ H : Subgroup G, P ≤ H → H ≤ X → H = P ∨ H = X
  hred : IsTwoReducedIn X U
  hUL : ⁅U, L⁆ = U
  hs : SumOfTwoNat L U α U₁ U₂ β₁ β₂
  hdyn : ∀ t ∈ T, ∃ l : ↥L, ∀ x y : ↥L, (y : G) = t * x * t⁻¹ →
      (QuotientGroup.mk y : ↥L ⧸ CFSG.pCore 2 ↥L) = QuotientGroup.mk (l * x * l⁻¹)

namespace burnsideC137_SCtx

variable [Finite G] {X T L P U U₁ U₂ : Subgroup G} {α : ↥L →* Γ}
  {β₁ : ↥U₁ →* Multiplicative Vec} {β₂ : ↥U₂ →* Multiplicative Vec}
  (h : burnsideC137_SCtx X T L P U α U₁ U₂ β₁ β₂)
include h


theorem hn : X ≤ normalizer (L : Set G) := C124.le_normalizer_of_prod h.hT h.hprod h.hL


omit [Finite G] in
theorem hU : IsElemAbelian 2 U := h.hred.2.2.1


end burnsideC137_SCtx

end CFSG.ASVolI
