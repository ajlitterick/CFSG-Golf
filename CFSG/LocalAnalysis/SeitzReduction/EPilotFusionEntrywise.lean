module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotHR4Basic
public import CFSG.LocalAnalysis.SeitzReduction.Fusion
public import CFSG.LieType.Chevalley.E6CanonicalFieldGraphFixed

public section

namespace CFSG.SeitzReduction.EPilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.SeitzReduction.F4Pilot (PerfectTwistedFusion)

variable {K : Type} [Field K]

theorem exists_ringEquiv_apply_eq_pow_two_pow {e : ℕ} (he : 1 ≤ e)
    (hK : Nat.card K = 2 ^ (2 * e)) : ∃ σ : K ≃+* K, ∀ c, σ c = c ^ 2 ^ e := by
  obtain ⟨fr, hfr, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two (by omega : 1 ≤ 2 * e) hK
  refine ⟨fr ^ e, fun c => ?_⟩
  clear hK he
  induction e with
  | zero => rw [pow_zero, RingAut.one_apply, pow_zero, pow_one]
  | succ n ih => rw [pow_succ', RingAut.mul_apply, ih, hfr, ← pow_mul, ← pow_succ]


variable {τ : Tag}

section Entrywise

variable (τ) in
noncomputable abbrev pinnedElt (α : Fin τ.rank → ℤ) (c : K) : adjointGroup τ K :=
  ⟨pinnedX τ K α c, pinnedX_mem_adjointGroup α c⟩

theorem entrywiseAdjointAut_pinnedElt (σ : K ≃+* K) (α : Fin τ.rank → ℤ) (c : K) :
    entrywiseAdjointAut τ σ (pinnedElt τ α c) = pinnedElt τ α (σ c) := by
  refine Subtype.ext (Units.ext ?_)
  rw [coe_entrywiseAdjointAut]
  exact entrywise_pinnedX σ.toRingHom α c


end Entrywise

section Fusion


end Fusion

end CFSG.SeitzReduction.EPilot
