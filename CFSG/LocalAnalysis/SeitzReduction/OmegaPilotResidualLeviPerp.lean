module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualLeviEqual
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualLeviSympChart
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualLeviWall

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Module Subgroup CFSG.Assembly.LowTwoRank
open LinearMap (BilinForm)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear

section Form

variable {K : Type} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}
  (N : (Fin d → K) →ₗ[K] (Fin d → K))
  (hadj : ∀ x y, QuadraticMap.polarBilin Q (N x) y = QuadraticMap.polarBilin Q x (N y))

abbrev kerForm : BilinForm K (LinearMap.ker N) :=
  (QuadraticMap.polarBilin Q).compl₁₂ (LinearMap.ker N).subtype (LinearMap.ker N).subtype

include hadj in
theorem rangeInKer_le_ker_kerForm : rangeInKer N ≤ LinearMap.ker (kerForm (Q := Q) N) := by
  intro a ha
  obtain ⟨x, hx⟩ := ha
  have hx' : N x = (a : Fin d → K) := hx
  rw [LinearMap.mem_ker]
  ext b
  change (QuadraticMap.polarBilin Q) (a : Fin d → K) (b : Fin d → K) = 0
  rw [← hx', hadj, LinearMap.mem_ker.mp b.2, map_zero]

include hadj in
theorem rangeInKer_le_ker_flip : rangeInKer N ≤ LinearMap.ker (kerForm (Q := Q) N).flip := by
  intro b hb
  obtain ⟨y, hy⟩ := hb
  have hy' : N y = (b : Fin d → K) := hy
  rw [LinearMap.mem_ker]
  ext a
  change (QuadraticMap.polarBilin Q) (a : Fin d → K) (b : Fin d → K) = 0
  rw [← hy', ← hadj, LinearMap.mem_ker.mp a.2, map_zero, LinearMap.zero_apply]

@[expose] noncomputable def kerQuotForm : BilinForm K (LinearMap.ker N ⧸ rangeInKer N) :=
  (kerForm (Q := Q) N).liftQ₂ (rangeInKer N) (rangeInKer N) (rangeInKer_le_ker_kerForm N hadj)
    (rangeInKer_le_ker_flip N hadj)

theorem kerQuotForm_mk (a b : LinearMap.ker N) :
    kerQuotForm N hadj (Submodule.Quotient.mk a) (Submodule.Quotient.mk b) =
      QuadraticMap.polar Q a b :=
  rfl

theorem kerQuotForm_isAlt [CharP K 2] : (kerQuotForm N hadj).IsAlt := by
  intro p
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ p
  rw [kerQuotForm_mk, QuadraticMap.polar_self, two_nsmul, CharTwo.add_self_eq_zero]

include hadj in
theorem mem_range_of_forall_polar (hB : (QuadraticMap.polarBilin Q).Nondegenerate)
    {z : Fin d → K} (hz : ∀ z' ∈ LinearMap.ker N, QuadraticMap.polar Q z' z = 0) :
    z ∈ LinearMap.range N := by
  have hrefl : (QuadraticMap.polarBilin Q).IsRefl := fun x y h => by
    rw [QuadraticMap.polarBilin_apply_apply] at h ⊢
    rw [QuadraticMap.polar_comm]
    exact h
  have hker : LinearMap.ker N =
      LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) (LinearMap.range N) := by
    ext v
    rw [mem_ker_iff_polar hB N hadj, LinearMap.BilinForm.mem_orthogonal_iff]
    constructor
    · rintro h _ ⟨x, rfl⟩
      exact h x
    · intro h x
      exact h _ (LinearMap.mem_range_self N x)
  rw [← LinearMap.BilinForm.orthogonal_orthogonal hB hrefl (LinearMap.range N), ← hker,
    LinearMap.BilinForm.mem_orthogonal_iff]
  intro z' hz'
  exact hz z' hz'

theorem kerQuotForm_nondegenerate (hB : (QuadraticMap.polarBilin Q).Nondegenerate) :
    (kerQuotForm N hadj).Nondegenerate := by
  have key : ∀ a : LinearMap.ker N, (∀ b : LinearMap.ker N, QuadraticMap.polar Q a b = 0) →
      (Submodule.Quotient.mk a : LinearMap.ker N ⧸ rangeInKer N) = 0 := by
    intro a h
    rw [Submodule.Quotient.mk_eq_zero]
    exact mem_range_of_forall_polar N hadj hB fun z' hz' => by
      rw [QuadraticMap.polar_comm]
      exact h ⟨z', hz'⟩
  constructor
  · intro p hp
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ p
    refine key a fun b => ?_
    have := hp (Submodule.Quotient.mk b)
    rwa [kerQuotForm_mk] at this
  · intro q hq
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    refine key b fun a => ?_
    have := hq (Submodule.Quotient.mk a)
    rwa [kerQuotForm_mk, QuadraticMap.polar_comm] at this

end Form

theorem kerQuotForm_map {K : Type} [Field K] [CharP K 2] {d : ℕ}
    {Q : QuadraticForm K (Fin d → K)} (hQ : ∃ v, Q v ≠ 0)
    {X : Subgroup (matrixProjectiveDerived Q)} (N : (Fin d → K) →ₗ[K] (Fin d → K))
    (hadj : ∀ x y, QuadraticMap.polarBilin Q (N x) y = QuadraticMap.polarBilin Q x (N y))
    (hXN : ∀ x ∈ X, ∀ v, projLift hQ x (N v) = N (projLift hQ x v)) (x : ↥X)
    (p q : LinearMap.ker N ⧸ rangeInKer N) :
    kerQuotForm N hadj (kerQuotHom hQ X N hXN x p) (kerQuotHom hQ X N hXN x q) =
      kerQuotForm N hadj p q := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ p
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  change kerQuotForm N hadj (kerQuotMap N _ (hXN x x.2) (Submodule.Quotient.mk a))
    (kerQuotMap N _ (hXN x x.2) (Submodule.Quotient.mk b)) = _
  rw [kerQuotMap_mk', kerQuotMap_mk', kerQuotForm_mk, kerQuotForm_mk]
  have h := polar_projLift hQ (x : matrixProjectiveDerived Q) a b
  rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polarBilin_apply_apply] at h
  exact h

section TypeBC

open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (coordinateQuadPlus regular_coordinateQuadPlus)


end TypeBC

end CFSG.SeitzReduction.OmegaPilot
