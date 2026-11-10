module

public import CFSG.Milestones.ASVolI.F429.aC3
public import CFSG.LocalAnalysis.EvenBN.U5.ModelFiveTwo

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin

section U5Line

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne.U5K.Hyp
  CFSG.LocalAnalysis.EvenBN.U5 CFSG.Quasithin.H13.Sec53F.Unit

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}

@[expose] def burnsideF429a_lev : HypIndex 2 1 → ℕ
  | .inl _ => 0
  | .inr (.inl _) => 1
  | .inr (.inr _) => 2

theorem burnsideF429a_mat_eq_zero_of_mem_u5LnStab {g : hypSU h 2 1} (hg : g ∈ u5LnStab h)
    (a c : HypIndex 2 1) (hac : burnsideF429a_lev c < burnsideF429a_lev a) : mat g a c = 0 := by
  have hG := (mem_u5LnStab_iff g).1 hg
  have hGi := (mem_u5LnStab_iff g⁻¹).1 (inv_mem hg)
  have hz1 : mat g ιf₁ ιz = 0 := by
    have h1 := hGi ιz ιe₁ (Or.inl rfl) (Or.inl rfl)
    rw [mat_inv_apply] at h1
    simpa using h1
  have hz2 : mat g ιf₂ ιz = 0 := by
    have h1 := hGi ιz ιe₂ (Or.inr rfl) (Or.inl rfl)
    rw [mat_inv_apply] at h1
    simpa using h1
  rcases H13.Sec53F.Unit.hypIndex_cases a with rfl | rfl | rfl | rfl | rfl <;>
    rcases H13.Sec53F.Unit.hypIndex_cases c with rfl | rfl | rfl | rfl | rfl <;>
    simp [burnsideF429a_lev] at hac <;>
    first
    | exact hz1
    | exact hz2
    | exact hG _ _ (Or.inl rfl) (Or.inl rfl)
    | exact hG _ _ (Or.inl rfl) (Or.inr (Or.inl rfl))
    | exact hG _ _ (Or.inl rfl) (Or.inr (Or.inr rfl))
    | exact hG _ _ (Or.inr rfl) (Or.inl rfl)
    | exact hG _ _ (Or.inr rfl) (Or.inr (Or.inl rfl))
    | exact hG _ _ (Or.inr rfl) (Or.inr (Or.inr rfl))

theorem burnsideF429a_mat_Ssub_apply {s : hypSU h 2 1} (hs : s ∈ Ssub h) (c d : HypIndex 2 1)
    (hcd : ¬ burnsideF429a_lev c < burnsideF429a_lev d) :
    mat s c d = (1 : Matrix (HypIndex 2 1) (HypIndex 2 1) K) c d := by
  obtain ⟨hsU, a1, a2⟩ := mem_Ssub'.1 hs
  obtain ⟨⟨d1, d2, d3, d4, d5⟩, ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10⟩⟩ := U_entries hsU
  rcases H13.Sec53F.Unit.hypIndex_cases c with rfl | rfl | rfl | rfl | rfl <;>
    rcases H13.Sec53F.Unit.hypIndex_cases d with rfl | rfl | rfl | rfl | rfl <;>
    simp_all [burnsideF429a_lev, ιe₁, ιe₂, ιz, ιf₁, ιf₂]

theorem burnsideF429a_fullPos_lt_of_lev_lt :
    ∀ a b : HypIndex 2 1, burnsideF429a_lev a < burnsideF429a_lev b → fullPos a < fullPos b := by
  decide

theorem burnsideF429a_conj_mem_Ssub {g s : hypSU h 2 1} (hg : g ∈ u5LnStab h) (hs : s ∈ Ssub h) :
    g * s * g⁻¹ ∈ Ssub h := by
  have hG := burnsideF429a_mat_eq_zero_of_mem_u5LnStab hg
  have hGi := burnsideF429a_mat_eq_zero_of_mem_u5LnStab (inv_mem hg)
  set E := mat s - 1 with hE
  have hEs : mat s = 1 + E := by rw [hE]; abel
  have hconj : mat (g * s * g⁻¹) = 1 + mat g * E * mat g⁻¹ := by
    rw [mat_mul, mat_mul, hEs, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, ← mat_mul,
      mul_inv_cancel, mat_one]
  have hEz : ∀ c d, ¬ burnsideF429a_lev c < burnsideF429a_lev d → E c d = 0 := by
    intro c d hcd
    rw [hE, Matrix.sub_apply, burnsideF429a_mat_Ssub_apply hs c d hcd, sub_self]
  have hent : ∀ a b, ¬ burnsideF429a_lev a < burnsideF429a_lev b →
      mat (g * s * g⁻¹) a b = (1 : Matrix (HypIndex 2 1) (HypIndex 2 1) K) a b := by
    intro a b hab
    rw [hconj, Matrix.add_apply]
    suffices (mat g * E * mat g⁻¹) a b = 0 by rw [this, add_zero]
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun d _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul]
    refine Finset.sum_eq_zero fun c _ => ?_
    by_cases hcd : burnsideF429a_lev c < burnsideF429a_lev d
    · by_cases hac : burnsideF429a_lev c < burnsideF429a_lev a
      · rw [hG a c hac, zero_mul, zero_mul]
      · have hdb : burnsideF429a_lev b < burnsideF429a_lev d := by omega
        rw [hGi d b hdb, mul_zero]
    · rw [hEz c d hcd]
      simp
  have hU : g * s * g⁻¹ ∈ hypUnitriangular h 2 1 := by
    rw [mem_hypUnitriangular]
    refine ⟨fun a b hab => ?_, fun a => ?_⟩
    · have hna : ¬ burnsideF429a_lev a < burnsideF429a_lev b := fun hlt =>
        (lt_asymm hab) (burnsideF429a_fullPos_lt_of_lev_lt a b hlt)
      change mat (g * s * g⁻¹) a b = 0
      rw [hent a b hna, one_apply_ne]
      rintro rfl
      exact (lt_irrefl _) hab
    · change mat (g * s * g⁻¹) a a = 1
      rw [hent a a (lt_irrefl _), one_apply_eq]
  refine mem_Ssub'.2 ⟨hU, ?_, ?_⟩
  · rw [hent _ _ (by simp [burnsideF429a_lev]), one_apply_ne (by decide)]
  · rw [hent _ _ (by simp [burnsideF429a_lev]), one_apply_ne (by decide)]


end U5Line

section U5Two

open CFSG.ClassicalGroups.UnitaryFlag CFSG.Quasithin.H13.Sec53F.Unit


end U5Two

end CFSG.ASVolI
