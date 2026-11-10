module

public import CFSG.Milestones.ASVolI.F431.BCoreGen
import all CFSG.Milestones.ASVolI.F4
public import CFSG.Quasithin.H13.U4ParOuter

public section

namespace CFSG.ASVolI

open CFSG.ASVolI.ChF CFSG.Quasithin Matrix CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.Quasithin.H13.U4Par
open scoped commutatorElement

section U4Model

variable {m : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 m K)

theorem burnsideF4m_U4_inr_mem (σ : K ≃+* K) :
    (SemidirectProduct.inr σ : SemiGL (HypIndex 2 0) K) ∈ semilinearSimilitudes h 2 0 :=
  ⟨1, one_ne_zero, map_one _, by
    rw [SemidirectProduct.left_inr]
    simp⟩

@[expose] noncomputable def burnsideF4m_U4_fieldElt (σ : K ≃+* K) (g : hypSU h 2 0) :
    hypSU h 2 0 :=
  ⟨glAut σ (g : GL (HypIndex 2 0) K), by
    have := conj_mem_hypSU (burnsideF4m_U4_inr_mem h σ) g
    simpa using this⟩

theorem burnsideF4m_U4_coe_fieldElt (σ : K ≃+* K) (g : hypSU h 2 0) :
    ((burnsideF4m_U4_fieldElt h σ g : hypSU h 2 0) : GL (HypIndex 2 0) K) =
      glAut σ (g : GL (HypIndex 2 0) K) := rfl

@[expose] noncomputable def burnsideF4m_U4_fieldAut : (K ≃+* K) →* MulAut (hypSU h 2 0) where
  toFun σ :=
    { toFun := burnsideF4m_U4_fieldElt h σ
      invFun := burnsideF4m_U4_fieldElt h σ⁻¹
      left_inv := fun g => Subtype.ext (by
        rw [burnsideF4m_U4_coe_fieldElt, burnsideF4m_U4_coe_fieldElt, ← MulAut.mul_apply,
          ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply])
      right_inv := fun g => Subtype.ext (by
        rw [burnsideF4m_U4_coe_fieldElt, burnsideF4m_U4_coe_fieldElt, ← MulAut.mul_apply,
          ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply])
      map_mul' := fun g g' => Subtype.ext (by
        rw [burnsideF4m_U4_coe_fieldElt, Subgroup.coe_mul, Subgroup.coe_mul, map_mul,
          burnsideF4m_U4_coe_fieldElt, burnsideF4m_U4_coe_fieldElt]) }
  map_one' := MulEquiv.ext fun g => Subtype.ext (by
    show glAut 1 (g : GL (HypIndex 2 0) K) = (g : GL (HypIndex 2 0) K)
    rw [map_one, MulAut.one_apply])
  map_mul' σ τ := MulEquiv.ext fun g => Subtype.ext (by
    show glAut (σ * τ) (g : GL (HypIndex 2 0) K) = glAut σ (glAut τ (g : GL (HypIndex 2 0) K))
    rw [map_mul, MulAut.mul_apply])

theorem burnsideF4m_U4_normalForm (θ : MulAut (hypSU h 2 0)) :
    ∃ (a : hypSU h 2 0) (σ : K ≃+* K), θ = MulAut.conj a * burnsideF4m_U4_fieldAut h σ := by
  let π := hypProj h 2 0
  let θ' : MulAut (hypPSU h 2 0) :=
    ((hypSUEquivPSU h).symm.trans θ).trans (hypSUEquivPSU h)
  have hπ : ∀ g, hypSUEquivPSU h g = π g := fun g => rfl
  have hθ' : ∀ g, θ' (π g) = π (θ g) := by
    intro g
    change hypSUEquivPSU h (θ ((hypSUEquivPSU h).symm (π g))) = π (θ g)
    rw [← hπ g, MulEquiv.symm_apply_apply, hπ]
  have hr : 1 ≤ 2 := by norm_num
  have hε : 0 ≤ 1 := by norm_num
  have hn4 : 3 ≤ 2 * 2 + 0 := by norm_num
  obtain ⟨x₀, hx₀⟩ := semilinearAutHom_surjective_of_admissible h hr hε hn4
    (fun h' => by omega) θ'
  obtain ⟨x₁, hx₁, -, hU⟩ := exists_unitary_rep h hr hε hn4 x₀
  rw [hx₀] at hx₁
  set A := (x₁ : SemiGL (HypIndex 2 0) K).left with hA
  set σ := (x₁ : SemiGL (HypIndex 2 0) K).right with hσ
  have hθA : ∀ g : hypSU h 2 0, ((θ g : hypSU h 2 0) : GL (HypIndex 2 0) K) =
      A * glAut σ (g : GL (HypIndex 2 0) K) * A⁻¹ := by
    intro g
    have h1 := semilinearAutHom_apply h hr hε x₁ g
    rw [hx₁, hθ'] at h1
    have h2 := hypProj_injective h h1
    exact congrArg Subtype.val h2
  obtain ⟨a, εu, hAa⟩ := exists_su_rep h hU
  have hc : ∀ X : GL (HypIndex 2 0) K, GeneralLinearGroup.scalar (HypIndex 2 0) εu * X =
      X * GeneralLinearGroup.scalar (HypIndex 2 0) εu := fun X => by
    ext i j
    simp [GeneralLinearGroup.coe_scalar, mul_comm]
  refine ⟨a, σ, MulEquiv.ext fun g => Subtype.ext ?_⟩
  rw [hθA g, hAa]
  show _ = (a : GL (HypIndex 2 0) K) * glAut σ (g : GL (HypIndex 2 0) K) *
    (a : GL (HypIndex 2 0) K)⁻¹
  have hcen : ∀ Y : GL (HypIndex 2 0) K, GeneralLinearGroup.scalar (HypIndex 2 0) εu * Y *
      (GeneralLinearGroup.scalar (HypIndex 2 0) εu)⁻¹ = Y := fun Y => by
    rw [hc Y, mul_assoc, mul_inv_cancel, mul_one]
  calc GeneralLinearGroup.scalar (HypIndex 2 0) εu * (a : GL (HypIndex 2 0) K) *
        glAut σ (g : GL (HypIndex 2 0) K) *
        (GeneralLinearGroup.scalar (HypIndex 2 0) εu * (a : GL (HypIndex 2 0) K))⁻¹ =
      GeneralLinearGroup.scalar (HypIndex 2 0) εu * ((a : GL (HypIndex 2 0) K) *
        glAut σ (g : GL (HypIndex 2 0) K) * (a : GL (HypIndex 2 0) K)⁻¹) *
        (GeneralLinearGroup.scalar (HypIndex 2 0) εu)⁻¹ := by group
    _ = _ := hcen _


end U4Model


end CFSG.ASVolI
