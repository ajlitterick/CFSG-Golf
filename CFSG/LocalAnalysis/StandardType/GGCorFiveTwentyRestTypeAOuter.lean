module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRestTypeA
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRestPerm

public section

namespace CFSG.StandardType

open CFSG.Assembly

namespace TypeA

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {d p : ℕ} {K : Type} [Field K]

section Main

variable [Finite K]

theorem ggTorusWeylNormInner_coprime [CharP K 2] (hp : p.Prime) (hp2 : p ≠ 2)
    (hpK : p ∣ Nat.card K - 1) (hd : 4 ≤ d) (hpd : Nat.Coprime p d) (hsec : SLHasSections d K) :
    GGTorusWeylNormInner p (d - 1) (projectiveSL d K) (Set.range (conjAut d K)) := by
  classical
  intro L' _ _ ψ hψ hker hperf A hA hAI hr _ φ₀ hφ₀
  obtain ⟨F, hFmul, hF1, hFswap, hFW, hFA, hFinj, hFsw⟩ :=
    exists_weylModel_psl hp hp2 hpK hd hpd hsec hψ hker hperf hA hAI hr
  have hex : ∀ σ, ∃ σ', φ₀ * F σ * φ₀⁻¹ = F σ' := fun σ =>
    let ⟨σ', h⟩ := hFW _ ((Subgroup.mem_normalizer_iff.mp hφ₀ (F σ)).mp (hFA σ))
    ⟨σ', h⟩
  choose α hα using hex
  have hαmul : ∀ σ τ, α (σ * τ) = α σ * α τ := by
    intro σ τ
    apply hFinj
    rw [← hα (σ * τ), hFmul σ τ, hFmul (α σ) (α τ), ← hα σ, ← hα τ]
    group
  let αh : Equiv.Perm (Fin d) →* Equiv.Perm (Fin d) :=
    { toFun := α
      map_one' := by
        apply hFinj
        rw [← hα 1, hF1]
        group
      map_mul' := hαmul }
  have hαh : ∀ σ, αh σ = α σ := fun _ => rfl
  have hαinj : Function.Injective αh := by
    intro σ τ h
    rw [hαh, hαh] at h
    apply hFinj
    have h1 : φ₀ * F σ * φ₀⁻¹ = φ₀ * F τ * φ₀⁻¹ := by
      rw [hα, hα, h]
    exact mul_left_cancel (mul_right_cancel h1)
  have hαswap : ∀ σ : Equiv.Perm (Fin d), σ.IsSwap → (αh σ).IsSwap := by
    rintro σ ⟨i, j, hij, rfl⟩
    rw [hαh]
    obtain ⟨-, -, -, -, hps⟩ := hFswap i j hij
    have h1 := hps.conj φ₀
    rw [hα] at h1
    exact hFsw _ h1
  obtain ⟨π₀, hπ₀⟩ := exists_eq_conj_of_isSwap (by omega) αh hαinj hαswap
  have hinv : F π₀ = (F π₀⁻¹)⁻¹ := by
    refine eq_inv_of_mul_eq_one_right ?_
    rw [← hFmul, mul_inv_cancel, hF1]
  refine ⟨F π₀⁻¹, hFA _, fun v hv => ?_⟩
  obtain ⟨σ, rfl⟩ := hFW v hv
  have hασ : α σ = π₀ * σ * π₀⁻¹ := by
    rw [← hαh]
    exact hπ₀ σ
  rw [hα, hασ, hFmul, hFmul, hinv]
  group


end Main


end TypeA


end CFSG.StandardType

end
