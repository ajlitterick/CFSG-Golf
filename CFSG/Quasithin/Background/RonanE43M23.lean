module

public import CFSG.Quasithin.Background.RonanE43M24
public import CFSG.Quasithin.Background.RonanE43Cyc23
public import CFSG.Quasithin.Background.HMathieuCode

public section

open scoped commutatorElement

namespace CFSG.Quasithin.RonanE43

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.Mathieu CFSG.Quasithin.E3
  CFSG.Monster.Code

section Simple

variable {X : Type} [Group X] [Finite X]

theorem generalizedFitting_eq_top_of_simple (hs : IsSimpleGroup X)
    (hnab : ∃ a b : X, a * b ≠ b * a) : CFSG.generalizedFitting X = ⊤ := by
  haveI := hs
  haveI hn : (CFSG.generalizedFitting X).Normal :=
    (CFSG.LocalCores.generalized_fitting_characteristic (G := X)).2
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (CFSG.generalizedFitting X) with h | h
  · exfalso
    have hle := CFSG.centralizer_generalizedFitting_le X
    rw [h] at hle
    obtain ⟨a, b, hab⟩ := hnab
    have hall : ∀ y : X, y = 1 := fun y => by
      have hy : y ∈ Subgroup.centralizer ((⊥ : Subgroup X) : Set X) := by
        rw [Subgroup.mem_centralizer_iff]
        intro g hg
        rw [SetLike.mem_coe, Subgroup.mem_bot] at hg
        rw [hg]
        simp
      exact Subgroup.mem_bot.mp (hle hy)
    exact hab (by rw [hall a, hall b])
  · exact h


end Simple


section Fixed


end Fixed

section Main


end Main

section Final


end Final

end CFSG.Quasithin.RonanE43
