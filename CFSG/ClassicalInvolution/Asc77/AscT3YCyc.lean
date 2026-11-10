module

public import CFSG.ClassicalInvolution.Asc77.AscT3YPsi
public import CFSG.ClassicalInvolution.Asc77.AscT3WInv

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

section Std

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}


theorem Std20.y_S_norm_X (d : Std20 p f K K' J S R R' W V z t) {s : G}
    (hs : s ∈ (S : Subgroup G)) {g : G} (hg : g ∈ sec20X (CoreAssembly.conjClass K) z K K') :
    s * g * s⁻¹ ∈ sec20X (CoreAssembly.conjClass K) z K K' :=
  (Subgroup.mem_normalizer_iff.mp (le_normalizer_sec20X d.hyp.conjInvariant d.viol.hzK d.twins
    (d.hSz hs)) g).mp hg

theorem Std20.y_cases (d : Std20 p f K K' J S R R' W V z t) {s : G}
    (hs : s ∈ (S : Subgroup G)) :
    s ∈ Subgroup.normalizer (K : Set G) ∨ conjSub s K = K' := by
  rcases d.late_conj_K (d.hSz hs) with h | h
  · exact Or.inl (mem_normalizer_iff_conjSub_eq.mpr h)
  · exact Or.inr h

theorem Std20.y_cyc_of_swapComm (d : Std20 p f K K' J S R R' W V z t) (c3 : Concl20_3 K K' V z)
    (c8 : Concl20_8 S K' R)
    (hsw : ∀ n ∈ (S : Subgroup G) ⊓ Subgroup.normalizer (K : Set G), ∀ w ∈ (S : Subgroup G),
      w ∉ Subgroup.normalizer (K : Set G) →
        ⁅n, w⁆ ∈ sec20X (CoreAssembly.conjClass K) z K K') :
    ∀ x ∈ (S : Subgroup G), ∀ y ∈ (S : Subgroup G),
      ⁅x, y⁆ ∈ sec20X (CoreAssembly.conjClass K) z K K' := by
  intro x hx y hy
  set X := sec20X (CoreAssembly.conjClass K) z K K' with hX
  by_cases hxN : x ∈ Subgroup.normalizer (K : Set G) <;>
    by_cases hyN : y ∈ Subgroup.normalizer (K : Set G)
  · exact d.y_comm_T c3 c8 ⟨hx, hxN⟩ ⟨hy, hyN⟩
  · exact hsw x ⟨hx, hxN⟩ y hy hyN
  · rw [← commutatorElement_inv]
    exact X.inv_mem (hsw y ⟨hy, hyN⟩ x hx hxN)
  · have hxK : conjSub x K = K' := (d.y_cases hx).resolve_left hxN
    have hyK : conjSub y K = K' := (d.y_cases hy).resolve_left hyN
    have hzN : x⁻¹ * y ∈ Subgroup.normalizer (K : Set G) := by
      rw [mem_normalizer_iff_conjSub_eq, conjSub_mul, hyK, ← hxK, conjSub_inv_conjSub]
    have hzS : x⁻¹ * y ∈ (S : Subgroup G) := S.mul_mem (S.inv_mem hx) hy
    have h1 := hsw (x⁻¹ * y) ⟨hzS, hzN⟩ x hx hxN
    have h2 : ⁅x, y⁆ = x * ⁅x, x⁻¹ * y⁆ * x⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [h2]
    have h3 : ⁅x, x⁻¹ * y⁆ ∈ X := by
      rw [← commutatorElement_inv]
      exact X.inv_mem h1
    exact d.y_S_norm_X hx h3


end Std

section Props


end Props

end CFSG.ClassicalInvolution.Asc77.T3CII
