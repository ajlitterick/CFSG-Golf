module

public import CFSG.LieType.Chevalley.CLSTwistedE6FieldTwoCover
public import CFSG.LieType.Chevalley.OddDiagramFrobeniusFixedDerived
public import CFSG.LieType.Chevalley.TwistedE6NormalForm

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.C2E6Overlap
  CFSG.LieType.Chevalley.C2E6Std
open Subgroup

theorem nonempty_mulEquiv_stdGroup_of_card_eq_four
    {L : Type} [Field L] [Finite L]
    (hL : Nat.card L = 4) (σ : L →+* L) (hσ : ∀ c, σ c = c ^ 2) :
    Nonempty (graphFixedRootGroup TwistTag.E6 L σ ≃* stdGroup) := by
  have : Fintype L := Fintype.ofFinite L
  set φ : K ≃+* L :=
    FiniteField.ringEquivOfCardEq (by rw [card_K, ← Nat.card_eq_fintype_card, hL]) with hφ
  have hcomm : ∀ c, σ (φ.toRingHom c) = φ.toRingHom (barHom c) := fun c => by
    rw [hσ, barHom_apply, bar]
    exact (map_pow _ c 2).symm
  have hbar : Function.Surjective barHom := fun a => ⟨bar a, (barHom_apply _).trans (bar_bar a)⟩
  have hσsurj : Function.Surjective σ := Finite.surjective_of_injective σ.injective
  have hpar : ∀ a, ∀ c ∈ orbitField TwistTag.E6 L σ a,
      ∃ c₀ ∈ orbitField TwistTag.E6 K barHom a, φ.toRingHom c₀ = c := by
    intro a c hc
    refine ⟨φ.symm c, ?_, φ.apply_symm_apply c⟩
    rw [mem_orbitField] at hc ⊢
    apply φ.injective
    change φ.toRingHom ((barHom ^ (TwistTag.E6.orbit a).card) (φ.symm c)) =
      φ.toRingHom (φ.symm c)
    rw [← ringHom_pow_apply_comm hcomm]
    change (σ ^ (TwistTag.E6.orbit a).card) (φ (φ.symm c)) = φ (φ.symm c)
    rw [φ.apply_symm_apply]
    exact hc
  have hmap : (graphFixedRootGroup TwistTag.E6 K barHom).map (baseChangeGL φ.toRingHom) =
      graphFixedRootGroup TwistTag.E6 L σ :=
    le_antisymm (map_baseChangeGL_graphFixedRootGroup_le hbar hcomm)
      (graphFixedRootGroup_le_map_baseChangeGL hσsurj hcomm hpar)
  exact ⟨((Subgroup.equivMapOfInjective (graphFixedRootGroup TwistTag.E6 K barHom)
    (baseChangeGL φ.toRingHom) (baseChangeGL_injective φ.toRingHom)).trans
      (MulEquiv.subgroupCongr hmap)).symm⟩


end CFSG.LieType.Chevalley
