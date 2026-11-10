module

public import CFSG.ClassicalInvolution.Generic.Generation.DeltaClosureLayer
import CFSG.ClassicalInvolution.Generic.InductionLocal
import CFSG.ClassicalInvolution.Generic.StepMember

public section

namespace CFSG.ClassicalInvolution.Generic.DeltaClosure

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {A : Subgroup G} {S : Set (Subgroup G)}

omit [Finite G] in
theorem isClassicalMember_conj_inv {L : Subgroup G} {z h : G}
    (hL : IsClassicalMember p f L (h * z * h⁻¹)) : IsClassicalMember p f (conjSub h⁻¹ L) z := by
  have := hL.conj h⁻¹
  have e : h⁻¹ * (h * z * h⁻¹) * h⁻¹⁻¹ = z := by group
  rwa [e] at this


end CFSG.ClassicalInvolution.Generic.DeltaClosure
