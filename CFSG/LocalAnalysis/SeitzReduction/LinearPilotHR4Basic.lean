module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotTwistedFusionBasic

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.EvenSmallLie CFSG.ComponentClassification.OuterAutomorphisms

section Transport

variable {X Y : Type*} [Group X] [Group Y]

theorem PerfectTwistedFusionIn.of_mulEquiv (e : X ≃* Y) {α : MulAut X} {β : MulAut Y}
    {Q : Y → Prop} (h : ∀ x, e (α x) = β (e x)) (hβ : PerfectTwistedFusionIn β Q) :
    PerfectTwistedFusionIn α fun x => Q (e x) := by
  obtain ⟨m, y, hy, hmy, hQ, P, hP, hyP, hPβ⟩ := hβ
  have h' : ∀ x, α (e.symm x) = e.symm (β x) := fun x => by
    apply e.injective
    rw [h, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
  refine ⟨e.symm m, e.symm y, fun h1 => hy ?_, ?_, ?_, P.map e.symm.toMonoidHom, ?_,
    ⟨y, hyP, rfl⟩, ?_⟩
  · rw [← e.apply_symm_apply y, h1, map_one]
  · rw [h', ← map_inv, ← map_mul, hmy]
  · show Q (e (e.symm y))
    rwa [MulEquiv.apply_symm_apply]
  · rw [← map_commutator, hP]
  · rintro _ ⟨p, hp, rfl⟩
    exact (h' p).trans (congrArg e.symm (hPβ p hp))


end Transport

section Standard

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}


omit [Finite G] in
theorem mem_conjugate_iff {g x : G} : x ∈ conjugate L g ↔ g * x * g⁻¹ ∈ L := by
  constructor
  · rintro ⟨l, hl, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    have he : g * (g⁻¹ * l * g) * g⁻¹ = l := by group
    rw [he]
    exact hl
  · intro h
    refine ⟨g * x * g⁻¹, h, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    group


end Standard

end CFSG.SeitzReduction.LinearPilot
