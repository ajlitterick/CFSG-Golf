module

public import CFSG.ClassicalInvolution.Q3.Q3TWModelB
public import CFSG.ClassicalInvolution.Q3.Q3WAE6Row

public section

namespace CFSG.ClassicalInvolution.Q3.Q3TW

open CFSG.LieType CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.RouteD CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.LieType.CurtisTits CFSG.LieType.Universal.Spin CFSG.Timmesfeld
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (SymplecticBlockStandardPair)
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.Q3W

set_option linter.unusedSectionVars false

theorem lieModel_of_surjective_simple3 {K G : Type} [Group K] [Group G] [IsSimpleGroup G]
    (hnab : ∃ x y : G, x * y ≠ y * x) (ψ : K →* G) (hsurj : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center K) {t : StatedLieTag} {n : ℕ}
    (hmodel : CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) t n 3 1) :
    CFSG.Blueprint.LieModel (G ⧸ Subgroup.center G) t n 3 1 := by
  have hZ : Subgroup.center G = ⊥ := CoreAssembly.center_eq_bot hnab
  have hZ' : Subgroup.center G = (Subgroup.center K).map ψ := by
    rw [hZ]
    symm
    rw [Subgroup.eq_bot_iff_forall]
    rintro _ ⟨k, hk, rfl⟩
    have h : ψ k ∈ Subgroup.center G := Subgroup.map_center_le_center hsurj ⟨k, hk, rfl⟩
    rw [hZ, Subgroup.mem_bot] at h
    exact h
  exact lieModel_of_mulEquiv (centerQuotientEquivOfSurjective ψ hsurj hker hZ') hmodel


end CFSG.ClassicalInvolution.Q3.Q3TW
