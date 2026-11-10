module

public import CFSG.ClassicalInvolution.Balance.StrongPowOrthGen
public import CFSG.ClassicalInvolution.Balance.StrongPowOrthLift
public import CFSG.ClassicalInvolution.Balance.LayerGenerationTransport

public section

namespace CFSG.ClassicalInvolution.Balance.StrongBalance.Orth

open QuadraticMap CFSG.ClassicalGroups.Orthogonal
open CFSG.Assembly.Dichotomy (involutionOddCore)
open CFSG.ClassicalInvolution.Balance (fixedGroup mem_fixedGroup)
open CFSG.ClassicalInvolution.ModelFacts (commutatorElement_mul_central)
open scoped commutatorElement

section FixLift

variable {K Γ : Type*} [Group K] [Group Γ]

theorem le_map_fixedGroup (θ : K →* Γ) (hker : θ.ker ≤ Subgroup.center K) (α : K ≃* K) (s : Γ)
    (hα : ∀ y, θ (α y) = s * θ y * s⁻¹) {N : Subgroup Γ} (hNp : ⁅N, N⁆ = N)
    (hNr : N ≤ θ.range) (hNs : ∀ n ∈ N, s * n = n * s) : N ≤ (fixedGroup α).map θ := by
  have hM : (N.comap θ).map θ = N := by
    rw [Subgroup.map_comap_eq, inf_eq_right.mpr hNr]
  have hcomm : ⁅N.comap θ, N.comap θ⁆ ≤ fixedGroup α := by
    refine Subgroup.commutator_le.mpr fun x hx y hy => ?_
    have hc : ∀ z : K, θ z ∈ N → z⁻¹ * α z ∈ Subgroup.center K := fun z hz => by
      refine hker ?_
      rw [MonoidHom.mem_ker, map_mul, map_inv, hα z, hNs _ hz]
      group
    rw [mem_fixedGroup, map_commutatorElement]
    have e₁ : α x = x * (x⁻¹ * α x) := by group
    have e₂ : α y = y * (y⁻¹ * α y) := by group
    rw [e₁, e₂]
    exact commutatorElement_mul_central (hc x hx) (hc y hy)
  calc N = ⁅N, N⁆ := hNp.symm
    _ = ⁅(N.comap θ).map θ, (N.comap θ).map θ⁆ := by rw [hM]
    _ = (⁅N.comap θ, N.comap θ⁆).map θ := (Subgroup.map_commutator _ _ _).symm
    _ ≤ (fixedGroup α).map θ := Subgroup.map_mono hcomm

end FixLift

section Quasisimple


end Quasisimple

section Side


end Side

end CFSG.ClassicalInvolution.Balance.StrongBalance.Orth
