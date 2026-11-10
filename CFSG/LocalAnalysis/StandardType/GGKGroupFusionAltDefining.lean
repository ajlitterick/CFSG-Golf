module

public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionAltLayer

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGLieParabolicCharInput : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (d : TauCeti.ValidLieTypeIndex),
    Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group) → d.1.characteristic ≠ 2 →
      ∀ S X : Subgroup K, IsPGroup d.1.characteristic S → ¬ d.1.characteristic ∣ S.index →
        Subgroup.normalizer (S : Set K) ≤ X → X ≠ ⊤ → IsCharacteristicP d.1.characteristic ↥X

@[expose] def GGLieOuterFieldAutInput : Prop :=
  ∀ (W : Type) [Group W] [Finite W] (E : Subgroup W) (d : TauCeti.ValidLieTypeIndex),
    IsSimpleGroup ↥(CFSG.generalizedFitting W) →
      (∃ a b : ↥(CFSG.generalizedFitting W), a * b ≠ b * a) →
        Nonempty (↥(CFSG.generalizedFitting W) ≃* (TauCeti.CFSGIndex.lie d).Group) →
          d.1.characteristic ≠ 2 → IsElemAbelian d.1.characteristic E →
            Nat.card E = d.1.characteristic ^ 2 → E ⊓ CFSG.generalizedFitting W = ⊥ →
              ∃ e ∈ E, e ≠ 1 ∧ ∀ Y : Subgroup W, Y ≤ CFSG.generalizedFitting W →
                Subgroup.centralizer ({e} : Set W) ⊓ CFSG.generalizedFitting W ≤ Y →
                  ¬ d.1.characteristic ∣ Y.relIndex (CFSG.generalizedFitting W) →
                    Y = CFSG.generalizedFitting W

section Inner

variable {W : Type} [Group W]

@[expose] def ggSubgroupOfEquivKer (H K : Subgroup W) [K.Normal] :
    ↥(H.subgroupOf K) ≃* ↥((QuotientGroup.mk' K).comp H.subtype).ker where
  toFun x := ⟨⟨((x : K) : W), Subgroup.mem_subgroupOf.mp x.2⟩,
    (ggMem_ker_mk_comp_subtype _).mpr (x : K).2⟩
  invFun y := ⟨⟨((y : H) : W), (ggMem_ker_mk_comp_subtype _).mp y.2⟩,
    Subgroup.mem_subgroupOf.mpr (y : H).2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem ggMem_normalizer_of_mem_normalizer_subgroupOf {S K : Subgroup W} (hSK : S ≤ K)
    {k : ↥K} (hk : k ∈ Subgroup.normalizer ((S.subgroupOf K : Subgroup K) : Set K)) :
    (k : W) ∈ Subgroup.normalizer (S : Set W) := by
  have h : (k : W) ∈ (Subgroup.normalizer ((S.subgroupOf K : Subgroup K) : Set K)).map
      K.subtype := Subgroup.mem_map_of_mem _ hk
  rw [CFSG.LocalAnalysis.ComponentInitial.map_normalizer_subgroupOf hSK] at h
  exact h.1

variable [Finite W]


end Inner

section Outer

variable {W : Type} [Group W] [Finite W]

theorem GGControlsStrongFusion.not_dvd_relIndex_inf {p : ℕ} [Fact p.Prime] {H E : Subgroup W}
    (h : GGControlsStrongFusion H E) (hE : IsElemAbelian p E) {e : W} (he : e ∈ E) (he1 : e ≠ 1)
    (K : Subgroup W) [K.Normal] : ¬ p ∣ (H ⊓ K).relIndex K := by
  obtain ⟨R, hRHK, -, hR⟩ := h.exists_sylow_le hE he he1
    (Subgroup.le_normalizer_of_normal (H := K) (Subgroup.mem_top e))
  intro hdvd
  apply hR
  rw [← Subgroup.relIndex_mul_relIndex R (H ⊓ K) K hRHK inf_le_right]
  exact Dvd.dvd.mul_left hdvd _


end Outer


end CFSG.StandardType
