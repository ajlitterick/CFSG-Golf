module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AltBig.Defs
public import CFSG.LocalAnalysis.QuasithinUnique.Defs

public section

namespace CFSG.QuasithinUnique.L246C127.AltBig

open Equiv Equiv.Perm Subgroup

variable {α : Type} [Fintype α] [DecidableEq α]

theorem sylApplyInv (σ : Perm α) (z : α) : σ (σ⁻¹ z) = z := by
  rw [← Perm.mul_apply, mul_inv_cancel, Perm.one_apply]

theorem sylInvApply (σ : Perm α) (z : α) : σ⁻¹ (σ z) = z := by
  rw [← Perm.mul_apply, inv_mul_cancel, Perm.one_apply]

theorem exists_fpfInv (hα : Even (Fintype.card α)) : Nonempty (FpfInv α) := by
  obtain ⟨r, hr⟩ := hα
  have hcard : Fintype.card α = Fintype.card (Fin r × Bool) := by
    simp only [hr, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
    omega
  let e : α ≃ Fin r × Bool := Fintype.equivOfCardEq hcard
  let μ' : Perm (Fin r × Bool) :=
    { toFun := fun z => (z.1, !z.2), invFun := fun z => (z.1, !z.2),
      left_inv := fun z => by simp, right_inv := fun z => by simp }
  have hμ'inv : ∀ z, μ' (μ' z) = z := by
    rintro ⟨i, b⟩
    simp [μ']
  have hμ'fpf : ∀ z, μ' z ≠ z := by
    rintro ⟨i, b⟩ h
    cases b <;> simp [μ'] at h
  refine ⟨⟨e.trans (μ'.trans e.symm), ?_, ?_⟩⟩
  · intro x
    simp [hμ'inv]
  · intro x h
    have h' : e.symm (μ' (e x)) = x := h
    have h'' : μ' (e x) = e x := by
      have := congrArg e h'
      simpa using this
    exact hμ'fpf (e x) h''

@[expose] def FpfInv.transport (p : FpfInv α) (σ : Perm α) : FpfInv α where
  μ := σ * p.μ * σ⁻¹
  inv x := by
    simp only [Perm.mul_apply, sylInvApply, sylApplyInv, p.inv]
  fpf x h := by
    apply p.fpf (σ⁻¹ x)
    have h' : σ (p.μ (σ⁻¹ x)) = x := h
    calc p.μ (σ⁻¹ x) = σ⁻¹ (σ (p.μ (σ⁻¹ x))) := (sylInvApply σ _).symm
      _ = σ⁻¹ x := by rw [h']

theorem FpfInv.transport_μ_apply (p : FpfInv α) (σ : Perm α) (x : α) :
    (p.transport σ).μ (σ x) = σ (p.μ x) := by
  change σ (p.μ (σ⁻¹ (σ x))) = σ (p.μ x)
  rw [sylInvApply]


end CFSG.QuasithinUnique.L246C127.AltBig
