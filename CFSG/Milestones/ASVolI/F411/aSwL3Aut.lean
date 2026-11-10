module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherConjAutInner

public noncomputable section

namespace CFSG.ASVolI

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

@[expose] def burnsideF411a_w0 (K : Type) [Field K] : GL (Fin 3) K where
  val := !![0, 0, 1; 0, 1, 0; 1, 0, 0]
  inv := !![0, 0, 1; 0, 1, 0; 1, 0, 0]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

variable {K : Type} [Field K]

theorem burnsideF411a_w0_mulVec (v : Fin 3 → K) :
    ((burnsideF411a_w0 K : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v = ![v 2, v 1, v 0] := by
  funext i
  fin_cases i <;> simp [burnsideF411a_w0, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem burnsideF411a_w0_mulVec_mulVec (v : Fin 3 → K) :
    ((burnsideF411a_w0 K : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
      (((burnsideF411a_w0 K : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v) = v := by
  rw [burnsideF411a_w0_mulVec, burnsideF411a_w0_mulVec]
  funext i
  fin_cases i <;> rfl

theorem burnsideF411a_w0_inv : (burnsideF411a_w0 K)⁻¹ = burnsideF411a_w0 K :=
  Units.ext rfl

theorem burnsideF411a_w0_mul_self : burnsideF411a_w0 K * burnsideF411a_w0 K = 1 := by
  conv_lhs => rw [← burnsideF411a_w0_inv (K := K)]
  exact inv_mul_cancel _

theorem burnsideF411a_inverseTranspose_w0 :
    GeneralLinearGroup.inverseTranspose (burnsideF411a_w0 K) = burnsideF411a_w0 K := by
  apply Units.ext
  rw [GeneralLinearGroup.coe_inverseTranspose, burnsideF411a_w0_inv]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl


theorem burnsideF411a_coordImage_flagSpace (σ : K ≃+* K) (d : ℕ) :
    coordImage σ (flagSpace 3 K d) = flagSpace 3 K d := by
  ext v
  rw [mem_coordImage, mem_flagSpace, mem_flagSpace]
  exact forall₂_congr fun j _ => by simp

theorem burnsideF411a_single_zero_mem : (Pi.single 0 1 : Fin 3 → K) ∈ flagSpace 3 K 1 := by
  rw [mem_flagSpace]
  intro j hj
  have hj0 : j ≠ 0 := fun h => by subst h; simp at hj
  simp [Pi.single_apply, hj0]

theorem burnsideF411a_single_one_mem : (Pi.single 1 1 : Fin 3 → K) ∈ flagSpace 3 K 2 := by
  rw [mem_flagSpace]
  intro j hj
  have hj1 : j ≠ 1 := fun h => by subst h; simp at hj
  simp [Pi.single_apply, hj1]

theorem burnsideF411a_flagSpace_one_le : flagSpace 3 K 1 ≤ flagSpace 3 K 2 := fun v hv =>
  mem_flagSpace.2 fun j hj => mem_flagSpace.1 hv j (by omega)

theorem burnsideF411a_w0_dotOrth_one :
    (dotOrth (flagSpace 3 K 1)).map
        (mulVecLin ((burnsideF411a_w0 K : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) =
      flagSpace 3 K 2 := by
  ext v
  rw [Submodule.mem_map, mem_flagSpace]
  constructor
  · rintro ⟨u, hu, rfl⟩ j hj
    rw [mem_dotOrth] at hu
    have h0 := hu _ burnsideF411a_single_zero_mem
    rw [dotProduct_single, mul_one] at h0
    have hj2 : j = 2 := Fin.ext (by have := j.2; omega)
    subst hj2
    rw [mulVecLin_apply, burnsideF411a_w0_mulVec]
    simpa using h0
  · intro hv
    refine ⟨((burnsideF411a_w0 K : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v, ?_, ?_⟩
    · rw [mem_dotOrth]
      intro w hw
      rw [mem_flagSpace] at hw
      have hw1 := hw 1 (by decide)
      have hw2 := hw 2 (by decide)
      have hv2 := hv 2 (by decide)
      rw [burnsideF411a_w0_mulVec]
      simp [dotProduct, Fin.sum_univ_three, hw1, hw2, hv2]
    · rw [mulVecLin_apply, burnsideF411a_w0_mulVec_mulVec]

theorem burnsideF411a_w0_dotOrth_two :
    (dotOrth (flagSpace 3 K 2)).map
        (mulVecLin ((burnsideF411a_w0 K : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) =
      flagSpace 3 K 1 := by
  ext v
  rw [Submodule.mem_map, mem_flagSpace]
  constructor
  · rintro ⟨u, hu, rfl⟩ j hj
    rw [mem_dotOrth] at hu
    have h0 := hu _ (burnsideF411a_flagSpace_one_le burnsideF411a_single_zero_mem)
    have h1 := hu _ burnsideF411a_single_one_mem
    rw [dotProduct_single, mul_one] at h0 h1
    rw [mulVecLin_apply, burnsideF411a_w0_mulVec]
    have hj' : j = 1 ∨ j = 2 := by
      rcases j with ⟨j, hj3⟩
      simp only [Fin.ext_iff]
      simp only at hj
      omega
    rcases hj' with rfl | rfl
    · simpa using h1
    · simpa using h0
  · intro hv
    refine ⟨((burnsideF411a_w0 K : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v, ?_, ?_⟩
    · rw [mem_dotOrth]
      intro w hw
      rw [mem_flagSpace] at hw
      have hw2 := hw 2 (by decide)
      have hv1 := hv 1 (by decide)
      have hv2 := hv 2 (by decide)
      rw [burnsideF411a_w0_mulVec]
      simp [dotProduct, Fin.sum_univ_three, hw2, hv1, hv2]
    · rw [mulVecLin_apply, burnsideF411a_w0_mulVec_mulVec]

variable (K) in
@[expose] noncomputable def burnsideF411a_L3zeta (τ : K ≃+* K) : MulAut (projectiveSL 3 K) :=
  conjAut 3 K (burnsideF411a_w0 K) * dualAut 3 K * fieldAut 3 K τ

theorem burnsideF411a_L3zeta_coe (τ : K ≃+* K) :
    (burnsideF411a_L3zeta K τ : projectiveSL 3 K →* projectiveSL 3 K) =
      (conjAut 3 K (burnsideF411a_w0 K) : projectiveSL 3 K →* projectiveSL 3 K).comp
        ((dualAut 3 K : projectiveSL 3 K →* projectiveSL 3 K).comp
          (fieldAut 3 K τ : projectiveSL 3 K →* projectiveSL 3 K)) :=
  MonoidHom.ext fun _ => rfl

theorem burnsideF411a_L3zeta_map_flag_one (τ : K ≃+* K) :
    (projStabilizer (flagSpace 3 K 1)).map
        (burnsideF411a_L3zeta K τ : projectiveSL 3 K →* projectiveSL 3 K) =
      projStabilizer (flagSpace 3 K 2) := by
  obtain ⟨-, -, -, -, -, -, hc, hf, hd, -⟩ := standard_automorphism_transport (K := K) (n := 3)
  rw [burnsideF411a_L3zeta_coe, ← Subgroup.map_map, ← Subgroup.map_map, hf,
    burnsideF411a_coordImage_flagSpace, hd, hc, burnsideF411a_w0_dotOrth_one]

theorem burnsideF411a_L3zeta_map_flag_two (τ : K ≃+* K) :
    (projStabilizer (flagSpace 3 K 2)).map
        (burnsideF411a_L3zeta K τ : projectiveSL 3 K →* projectiveSL 3 K) =
      projStabilizer (flagSpace 3 K 1) := by
  obtain ⟨-, -, -, -, -, -, hc, hf, hd, -⟩ := standard_automorphism_transport (K := K) (n := 3)
  rw [burnsideF411a_L3zeta_coe, ← Subgroup.map_map, ← Subgroup.map_map, hf,
    burnsideF411a_coordImage_flagSpace, hd, hc, burnsideF411a_w0_dotOrth_two]


end CFSG.ASVolI
