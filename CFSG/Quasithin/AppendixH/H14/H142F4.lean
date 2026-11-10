module

public import CFSG.GH74.KGroups.FieldGF
public import CFSG.Quasithin.AppendixH.H14.Vocab

public section

namespace CFSG.Quasithin.AppendixH.H14

open CFSG.GH74.KGroups CFSG.ASVolI.ChH

lemma gf4_eq_cases (c : GF4) : c = 0 ∨ c = 1 ∨ c = GF4.ofNat' 2 ∨ c = GF4.ofNat' 3 := by
  fin_cases c <;> decide

lemma gf4_root_sq_add_self_add_one :
    ∀ s : GF4, s * s + s + 1 = 0 → s = GF4.ofNat' 2 ∨ s = GF4.ofNat' 3 := by
  decide


@[expose] def frobGF4 : GF4 ≃+* GF4 where
  toFun c := c * c
  invFun c := c * c
  left_inv := by decide
  right_inv := by decide
  map_mul' := by decide
  map_add' := by decide

theorem ringEquiv_gf4_cases (σ : GF4 ≃+* GF4) : σ = RingEquiv.refl GF4 ∨ σ = frobGF4 := by
  have hs : σ (GF4.ofNat' 2) * σ (GF4.ofNat' 2) + σ (GF4.ofNat' 2) + 1 = 0 := by
    have h2 : GF4.ofNat' 2 * GF4.ofNat' 2 + GF4.ofNat' 2 + 1 = 0 := by decide
    simpa using congrArg σ h2
  have h3 : GF4.ofNat' 3 = GF4.ofNat' 2 + 1 := by decide
  rcases gf4_root_sq_add_self_add_one _ hs with h | h
  · left
    ext c
    rcases gf4_eq_cases c with hc | hc | hc | hc
    · subst hc; simp
    · subst hc; simp
    · subst hc; simpa using h
    · subst hc
      rw [h3, map_add, map_one, h]
      simp
  · right
    ext c
    rcases gf4_eq_cases c with hc | hc | hc | hc
    · subst hc; simp
    · subst hc; simp
    · subst hc; rw [h]; decide
    · subst hc
      rw [h3, map_add, map_one, h]
      decide


end CFSG.Quasithin.AppendixH.H14
