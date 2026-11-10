module

public import CFSG.GH74.Uniqueness.Section5Prop52

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

omit [Finite X] in
theorem IsMaxFixingThree.map_conjugate {p : ℕ} {P : Subgroup X} (hP : IsMaxFixingThree M p P)
    (g : X) : IsMaxFixingThree M p (conjugate P g) := by
  refine ⟨⟨isPGroup_conjugate hP.1.1 g, by rw [ncard_omegaFix_conjugate]; exact hP.1.2⟩,
    fun Q hQ hle => ?_⟩
  have hQ' : IsPGroup p (conjugate Q g⁻¹) ∧
      3 ≤ (omegaFix M ((conjugate Q g⁻¹ : Subgroup X) : Set X)).ncard :=
    ⟨isPGroup_conjugate hQ.1 g⁻¹, by rw [ncard_omegaFix_conjugate]; exact hQ.2⟩
  have hle' : P ≤ conjugate Q g⁻¹ := by
    have := conjugate_mono hle g⁻¹
    rwa [conjugate_conjugate_inv] at this
  have := conjugate_mono (hP.2 hQ' hle') g
  rwa [conjugate_inv_conjugate] at this


omit [Finite X] in
theorem card_fixedPointsOfSubgroup_omega (U : Subgroup X) :
    Nat.card {ω : omega M // ω ∈ CFSG.BenderSuzuki.PFchapter1section1.fixedPointsOfSubgroup X (omega M) U} =
      (omegaFix M (U : Set X)).ncard := by
  rw [← Nat.card_coe_set_eq]
  refine Nat.card_congr
    { toFun := fun ω => ⟨ω.1.1, ω.1.2, fun g hg => by
        have := congrArg (fun γ : omega M => (γ : Subgroup X)) (ω.2 g⁻¹ (U.inv_mem hg))
        simpa [omegaMulAction_smul_coe] using this⟩
      invFun := fun β => ⟨⟨β.1, β.2.1⟩, fun x hx => Subtype.ext (by
        show conjugate β.1 x⁻¹ = β.1
        exact β.2.2 _ (U.inv_mem hx))⟩
      left_inv := fun ω => rfl
      right_inv := fun β => rfl }


end CFSG.GH74.Uniqueness
