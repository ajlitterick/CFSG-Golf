module

public import CFSG.ClassicalInvolution.Q3.Tight
public import CFSG.ClassicalInvolution.Q3.TL3Sub
public import CFSG.ClassicalInvolution.Q3.TL3Lift
public import CFSG.ClassicalInvolution.Q3.TL3QuatAut

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open scoped commutatorElement


theorem tl3_nonempty_mulEquiv_q8 {G : Type*} [Group G] [Finite G] {R : Subgroup G}
    (S : Sylow 2 R)
    (hS : ∃ r : ℕ, 3 ≤ r ∧ Nonempty ((S : Subgroup R) ≃* QuaternionGroup (2 ^ (r - 2))))
    (h2 : IsPGroup 2 (R ⧸ classicalInvolutionOddCore R)) {C : Subgroup G}
    (hCR : C ≤ Subgroup.normalizer (R : Set G)) {x : G} (hxC : x ∈ C) {k : ℕ}
    (hx3 : x ^ 3 ^ k = 1) (hxR : ∃ r ∈ R, ⁅x, r⁆ ∉ oddCoreImg R) :
    Nonempty ((S : Subgroup R) ≃* QuaternionGroup 2) := by
  obtain ⟨r, hr, ⟨e⟩⟩ := hS
  by_cases hr3 : r = 3
  · subst hr3
    exact ⟨e⟩
  · exfalso
    have hr4 : 2 ≤ r - 2 := by omega
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨e1⟩ := QuaternionStructure.nonempty_mulEquiv_sylow_of_isPGroup_oddCore_quotient h2 S
    set P : MulAut (R ⧸ oddCore R) := tl3Act R ⟨x, hCR hxC⟩ with hP
    have hPk : P ^ 3 ^ k = 1 := by
      rw [hP, ← map_pow]
      have : (⟨x, hCR hxC⟩ : Subgroup.normalizer (R : Set G)) ^ 3 ^ k = 1 :=
        Subtype.ext (by simpa using hx3)
      rw [this, map_one]
    have hP1 : P = 1 := tl3_aut_pow_three_of_equiv hr4 (e1.trans e) P hPk
    obtain ⟨r', hr', hnr⟩ := hxR
    exact hnr ((tl3Act_eq_one_iff R ⟨x, hCR hxC⟩).mp hP1 r' hr')


end CFSG.ClassicalInvolution.Q3
