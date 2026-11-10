module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4P1Check
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Sporadic.SmallOddCore.CentSpec

public section

namespace CFSG.ComponentClassification.HarrisLit.P1

open CFSG Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier

variable {n : ℕ}


structure RowFacts (A₀ : Subgroup (Equiv.Perm (Fin n))) (r : ClassRow) : Prop where
  rep : Rep n r.rep (tp n r.rep)
  ord : orderOf (tp n r.rep) = 2
  outer : r.outer = true ↔ tp n r.rep ∉ A₀
  cent : closure (tp n '' {x | x ∈ r.centGens.toArray}) =
    A₀ ⊓ centralizer ({tp n r.rep} : Set (Equiv.Perm (Fin n)))
  card : Nat.card ↥(A₀ ⊓ centralizer ({tp n r.rep} : Set (Equiv.Perm (Fin n)))) = r.centOrder
  cls : (Sporadic.SmallOddCore.conjClass A₀ (tp n r.rep)).ncard = r.classSize

structure RunFacts (A₀ : Subgroup (Equiv.Perm (Fin n))) (R : Run) : Prop where
  repu : Rep n R.u (tp n R.u)
  repuinv : Rep n (invT n R.u) (tp n R.u)⁻¹
  u2 : tp n R.u ^ 2 = 1
  uout : tp n R.u ∉ A₀
  unorm : ∀ p ∈ A₀, tp n R.u * p * (tp n R.u)⁻¹ ∈ A₀
  memR : ∀ x, x ∈ A₀ ⊔ zpowers (tp n R.u) ↔ x ∈ A₀ ∨ x * tp n R.u ∈ A₀
  row : ∀ r ∈ R.rows, RowFacts A₀ r.row
  cover : ∀ t ∈ A₀ ⊔ zpowers (tp n R.u), orderOf t = 2 →
    ∃ r ∈ R.rows, ∃ g ∈ A₀, t = g * tp n r.row.rep * g⁻¹


end CFSG.ComponentClassification.HarrisLit.P1
