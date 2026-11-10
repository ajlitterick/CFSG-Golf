module

public import CFSG.LieType.Steinberg.Isogeny.E6
import CFSG.LocalAnalysis.StandardType.GGTBE6Cover
public import CFSG.LieType.Chevalley.RootCommutatorData

public section

set_option linter.unusedSectionVars false

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.Isogeny


theorem kgLangS1EFixedLift_splitCover (k : Type) [Field k] [Finite k] [CharP k 2]
    (hk : 5 ≤ Nat.card k) (R : Type) [Group R] (ε : R ≃* ↥(adjointGroup Tag.E6 k))
    (K : Type) [Group K] [Finite K] (θ : K ⧸ Subgroup.center K ≃* R) (hK : commutator K = ⊤)
    (α : MulAut K) :
    ∃ (κ : ↥(e6Data_valid.minGroup k) →* K) (αU : MulAut ↥(e6Data_valid.minGroup k)),
      Function.Surjective κ ∧
      (∀ u, ((ε (θ (QuotientGroup.mk (κ u))) : ↥(adjointGroup Tag.E6 k)) : ModGL Tag.E6 k) =
        ((e6Isogeny k u : ↥(adjointGroup Tag.E6 k)) : ModGL Tag.E6 k)) ∧
      (∀ u, κ (αU u) = α (κ u)) := by
  classical
  let ψ : K →* ↥(adjointGroup Tag.E6 k) :=
    ε.toMonoidHom.comp (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K)))
  have hψs : Function.Surjective ψ :=
    ε.surjective.comp (θ.surjective.comp (QuotientGroup.mk'_surjective _))
  have hψk : ψ.ker ≤ Subgroup.center K := by
    intro x hx
    have h1 : (QuotientGroup.mk x : K ⧸ Subgroup.center K) = 1 := by
      have hx' : ε (θ (QuotientGroup.mk x)) = 1 := hx
      exact θ.injective (ε.injective (by rw [hx', map_one, map_one]))
    exact (QuotientGroup.eq_one_iff x).mp h1
  obtain ⟨κ, hκs, hκψ, hκker⟩ :=
    CFSG.LocalAnalysis.StandardType.GGTBE6Cover.exists_cover_phi k K ψ hψs hψk hK
  have hperfU : commutator ↥(e6Data_valid.minGroup k) = ⊤ :=
    (CFSG.LieType.CurtisTits.isPerfect_e6 k).commutator_eq_top
  obtain ⟨αU, hαU⟩ :=
    CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6.exists_lift_aut κ hκs hκker hperfU
      (fun E _ _ p hp hcen =>
        CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.e6_exists_section_of_central hk hp hcen)
      α
  exact ⟨κ, αU, hκs, fun u => congrArg Subtype.val (hκψ u), hαU⟩

end CFSG.StandardType
