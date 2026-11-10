module

public import CFSG.ClassicalInvolution.Balance.Delta

public section

namespace CFSG.ClassicalInvolution.Balance

open CFSG.Open CFSG.Assembly.Dichotomy CFSG.ComponentClassification
open scoped commutatorElement

section StepOne

variable {G : Type*} [Group G] [Finite G]

theorem le_centralizer_oddCoreIn_inf_centralizer {C K E₀ L₀ F : Subgroup G}
    (hKC : IsSubnormal K C) (hFE : F ≤ E₀) (hL₀K : L₀ ≤ K)
    (hL₀E : L₀ ≤ Subgroup.centralizer (E₀ : Set G)) (hL₀ : commutator L₀ = ⊤)
    (hΔ : deltaCore F = ⊥)
    (hB : ∀ f ∈ F, f ≠ 1 →
      ⁅oddCoreIn (normalClosureIn (C ⊓ Subgroup.centralizer {f}) L₀),
        normalClosureIn (C ⊓ Subgroup.centralizer {f}) L₀⁆ ≤ involutionOddCore f) :
    L₀ ≤ Subgroup.centralizer ((oddCoreIn K ⊓ Subgroup.centralizer (F : Set G) : Subgroup G) :
      Set G) := by
  set V : Subgroup G := oddCoreIn K ⊓ Subgroup.centralizer (F : Set G) with hV
  have hVodd : Odd (Nat.card V) :=
    (odd_card_oddCoreIn K).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  have hKC' : K ≤ C := isSubnormal_le hKC
  have hOC : IsSubnormal (oddCoreIn K) C := isSubnormal_trans (isSubnormal_oddCoreIn K) hKC
  have hconj : ∀ q ∈ L₀, ∀ v ∈ V, q * v * q⁻¹ ∈ V := by
    intro q hq v hv
    refine ⟨conj_mem_oddCoreIn (hL₀K hq) hv.1, ?_⟩
    show q * v * q⁻¹ ∈ Subgroup.centralizer (F : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have hhq : Commute h q := Subgroup.mem_centralizer_iff.mp (hL₀E hq) h (hFE hh)
    have hhv : Commute h v := Subgroup.mem_centralizer_iff.mp hv.2 h hh
    exact ((hhq.mul_right hhv).mul_right hhq.inv_right).eq
  refine le_of_perfect_of_forall_isPGroup_le hL₀ fun P hPL hP => ?_
  have hPnorm : P ≤ Subgroup.normalizer (V : Set G) := by
    intro p hp
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => hconj p (hPL hp) y hy, fun hy => ?_⟩
    have h2 := hconj p⁻¹ (inv_mem (hPL hp)) _ hy
    have h3 : p⁻¹ * (p * y * p⁻¹) * (p⁻¹)⁻¹ = y := by group
    rwa [h3] at h2
  have hcomm : ⁅V, P⁆ = ⊥ := by
    have h1 : ⁅⁅V, P⁆, P⁆ = ⁅V, P⁆ := commutator_commutator_eq_of_isPGroup hP hVodd hPnorm
    rw [eq_bot_iff, ← hΔ]
    refine le_deltaCore fun f hf hf1 => ?_
    set Nf := normalClosureIn (C ⊓ Subgroup.centralizer {f}) L₀ with hNf
    have hL₀le : L₀ ≤ C ⊓ Subgroup.centralizer {f} := by
      refine le_inf (hL₀K.trans hKC') fun l hl => ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp (hL₀E hl) f (hFE hf)).symm
    have hNfle : Nf ≤ C ⊓ Subgroup.centralizer {f} := normalClosureIn_le_of_le hL₀le
    have hsub : IsSubnormal (oddCoreIn K ⊓ Nf) Nf := by
      have := isSubnormal_inf hOC Nf
      rwa [inf_eq_right.mpr (hNfle.trans inf_le_left)] at this
    have hle := le_oddCoreIn_of_isSubnormal hsub
      ((odd_card_oddCoreIn K).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left))
    have hVNf : ⁅V, P⁆ ≤ oddCoreIn Nf := by
      refine le_trans ?_ hle
      rw [Subgroup.commutator_le]
      intro v hv p hp
      have hpK : p ∈ K := hL₀K (hPL hp)
      have hvC : v ∈ C ⊓ Subgroup.centralizer {f} := by
        refine ⟨hKC' (oddCoreIn_le K hv.1), ?_⟩
        show v ∈ Subgroup.centralizer {f}
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_iff.mp hv.2 f hf).symm
      have hpNf : p ∈ Nf := le_normalClosureIn _ _ (hPL hp)
      refine ⟨?_, ?_⟩
      · have : ⁅v, p⁆ = v * (p * v⁻¹ * p⁻¹) := by simp [commutatorElement_def, mul_assoc]
        rw [this]
        exact (oddCoreIn K).mul_mem hv.1 (conj_mem_oddCoreIn hpK ((oddCoreIn K).inv_mem hv.1))
      · exact Nf.mul_mem (conj_mem_normalClosureIn hvC hpNf) (Nf.inv_mem hpNf)
    calc ⁅V, P⁆ = ⁅⁅V, P⁆, P⁆ := h1.symm
      _ ≤ ⁅oddCoreIn Nf, Nf⁆ :=
        Subgroup.commutator_mono hVNf (hPL.trans (le_normalClosureIn _ _))
      _ ≤ involutionOddCore f := hB f hf hf1
  have hcomm' : ⁅P, V⁆ = ⊥ := by rw [Subgroup.commutator_comm]; exact hcomm
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm'

end StepOne

section StepTwo

variable {G : Type*} [Group G] [Finite G]

theorem le_centralizer_oddCoreIn {C K E₀ L₀ : Subgroup G} (hKC : IsSubnormal K C)
    (hE₀K : E₀ ≤ K) (hE₀ : IsElemAbelian 2 E₀) (hE₀card : Nat.card E₀ = 8) (hL₀K : L₀ ≤ K)
    (hL₀E : L₀ ≤ Subgroup.centralizer (E₀ : Set G)) (hL₀ : commutator L₀ = ⊤)
    (hΔ : ∀ F ∈ signalizerFunctorEk 2 2 E₀, deltaCore F = ⊥)
    (hB : ∀ f ∈ E₀, f ≠ 1 →
      ⁅oddCoreIn (normalClosureIn (C ⊓ Subgroup.centralizer {f}) L₀),
        normalClosureIn (C ⊓ Subgroup.centralizer {f}) L₀⁆ ≤ involutionOddCore f) :
    L₀ ≤ Subgroup.centralizer (oddCoreIn K : Set G) := by
  have hgen := CFSG.SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation 2 2
    Nat.prime_two E₀ (oddCoreIn K) hE₀ (by rw [hE₀card]; norm_num)
    (hE₀K.trans (normalizer_oddCoreIn K))
    (Nat.coprime_two_left.mpr (odd_card_oddCoreIn K))
  have h1 : oddCoreIn K ≤ Subgroup.centralizer (L₀ : Set G) := by
    refine hgen.symm.le.trans (iSup₂_le fun F hF => ?_)
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have hlv := le_centralizer_oddCoreIn_inf_centralizer hKC hF.1 hL₀K hL₀E hL₀ (hΔ F hF)
      (fun f hf hf1 => hB f (hF.1 hf) hf1) hl
    exact (Subgroup.mem_centralizer_iff.mp hlv v hv).symm
  intro l hl
  rw [Subgroup.mem_centralizer_iff]
  intro o ho
  exact (Subgroup.mem_centralizer_iff.mp (h1 ho) l hl).symm

end StepTwo

section StepThree


end StepThree

section Chain


end Chain

end CFSG.ClassicalInvolution.Balance
