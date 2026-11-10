module

public import CFSG.Monster.AxisCount.Abstract
public import CFSG.Monster.Visible.Pair

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.AxisCount

open CFSG.Monster CFSG.Monster.Griess CFSG.Monster.ScalarKernel CFSG.Monster.Visible Matrix

@[expose] def trA2 (v : SpaceB) : ℚ :=
  ∑ i : Fin 24, ∑ j : Fin 24, ((v.1 : Matrix (Fin 24) (Fin 24) ℚ) i j) ^ 2

theorem sumSq_eq_trace (M : Matrix (Fin 24) (Fin 24) ℚ) :
    ∑ i, ∑ j, M i j ^ 2 = Matrix.trace (M * Mᵀ) := by
  simp [Matrix.trace, Matrix.mul_apply, pow_two]


theorem sumSq_conj (g A : Matrix (Fin 24) (Fin 24) ℚ) (hg : g * gᵀ = 1) :
    ∑ i, ∑ j, (gᵀ * A * g) i j ^ 2 = ∑ i, ∑ j, A i j ^ 2 := by
  rw [sumSq_eq_trace, sumSq_eq_trace]
  have e : gᵀ * A * g * (gᵀ * A * g)ᵀ = gᵀ * (A * Aᵀ) * g := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
    calc gᵀ * A * g * (gᵀ * (Aᵀ * g)) = gᵀ * A * (g * gᵀ) * (Aᵀ * g) := by
          simp only [Matrix.mul_assoc]
      _ = gᵀ * (A * Aᵀ) * g := by
          rw [hg, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
  rw [e, Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hg, Matrix.one_mul]

theorem trA2_theta (p : Pvis) (v : SpaceB) : trA2 (theta p v) = trA2 v := by
  rw [trA2, trA2, theta_apply]
  exact sumSq_conj _ _ (mat_mul_transpose p.1.2)


theorem trA2_apply_of_mem_Gvis {g : SpaceB ≃ₗ[ℚ] SpaceB} (hg : g ∈ Gvis) (v : SpaceB) :
    trA2 (g v) = trA2 v := by
  obtain ⟨p, rfl⟩ := mem_Gvis.1 hg
  exact trA2_theta p v

theorem trA2_smul_of_mem_Gvis {g : SpaceB ≃ₗ[ℚ] SpaceB} (hg : g ∈ Gvis) (v : SpaceB) :
    trA2 (g • v) = trA2 v :=
  trA2_apply_of_mem_Gvis hg v


theorem Setup.orb_injective_of_trA2 {I : Type*} {R : I → Type*}
    (S : Setup (SpaceB ≃ₗ[ℚ] SpaceB) SpaceB I R) (hH : S.H ≤ Gvis)
    (hinj : Function.Injective fun i => trA2 (S.v i)) : Function.Injective S.orb :=
  S.orb_injective_of_invariant trA2 (fun _ hc x => trA2_smul_of_mem_Gvis (hH hc) x) hinj


end CFSG.Monster.AxisCount
