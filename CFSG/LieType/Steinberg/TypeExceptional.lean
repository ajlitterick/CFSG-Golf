module

public import CFSG.LieType.Steinberg.Basic
public import CFSG.Blueprint.ChevalleyStrings

public section

namespace CFSG.LieType.Steinberg

open CFSG.Blueprint.Chevalley

namespace TagRoots

variable {τ : Tag}

theorem isRoot_neg {v : Fin τ.rank → ℤ} (hv : IsRoot τ v) : IsRoot τ (-v) := by
  induction hv with
  | basis j => exact isRoot_neg_single τ j
  | @reflect i w _ ih =>
    have h : -reflect τ i w = reflect τ i (-w) := by
      rw [← reflectHom_apply, ← reflectHom_apply, map_neg]
    exact h ▸ IsRoot.reflect i ih

theorem eq_or_eq_neg_of_not_linIndepPair {γ δ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ)
    (hδ : IsRoot τ δ) (h : ¬ LinIndepPair γ δ) : γ = δ ∨ γ = -δ := by
  simp only [LinIndepPair, not_forall] at h
  obtain ⟨a, b, hab, hne⟩ := h
  obtain ⟨j, f, hf⟩ := hδ.exists_addMonoidHom_eq_single
  obtain ⟨i, g, hg⟩ := hγ.exists_addMonoidHom_eq_single
  have ha : a ≠ 0 := by
    rintro rfl
    have hb : b ≠ 0 := fun hb => hne ⟨rfl, hb⟩
    have : b • δ = 0 := by simpa using hab
    exact hδ.ne_zero ((smul_eq_zero.1 this).resolve_left hb)
  have hb : b ≠ 0 := by
    rintro rfl
    have : a • γ = 0 := by simpa using hab
    exact hγ.ne_zero ((smul_eq_zero.1 this).resolve_left ha)
  have hfγ : a • f γ = -(b • Pi.single j 1) := by
    have := congrArg f hab
    rw [map_add, map_zsmul, map_zsmul, hf, map_zero] at this
    exact eq_neg_of_add_eq_zero_left this
  have hgδ : b • g δ = -(a • Pi.single i 1) := by
    have := congrArg g hab
    rw [map_add, map_zsmul, map_zsmul, hg, map_zero] at this
    exact eq_neg_of_add_eq_zero_right this
  have hm : a * f γ j = -b := by simpa using congrFun hfγ j
  have hm' : b * g δ i = -a := by simpa using congrFun hgδ i
  have hmm : f γ j * g δ i = 1 := by
    have h1 : a * (f γ j * g δ i) = a := by
      calc a * (f γ j * g δ i) = (a * f γ j) * g δ i := by ring
        _ = -(b * g δ i) := by rw [hm]; ring
        _ = a := by rw [hm']; ring
    have := mul_left_cancel₀ ha (h1.trans (mul_one a).symm)
    exact this
  have hγδ : a • (γ - f γ j • δ) = 0 := by
    rw [smul_sub, smul_smul, hm, neg_smul, sub_neg_eq_add, add_comm]
    simpa [add_comm] using hab
  have hγeq : γ = f γ j • δ := sub_eq_zero.1 ((smul_eq_zero.1 hγδ).resolve_left ha)
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hmm with h1 | h1
  · left; rw [hγeq, h1, one_smul]
  · right; rw [hγeq, h1, neg_one_smul]

theorem exists_word {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) :
    ∃ (w : List (Fin τ.rank)) (i : Fin τ.rank),
      γ = wordAct (reflectHom τ) w (Pi.single i 1) := by
  induction hγ with
  | basis j => exact ⟨[], j, rfl⟩
  | reflect i _ ih =>
    obtain ⟨w, j, hw⟩ := ih
    exact ⟨i :: w, j, by simp only [wordAct, hw, reflectHom_apply]⟩


end TagRoots


end CFSG.LieType.Steinberg
