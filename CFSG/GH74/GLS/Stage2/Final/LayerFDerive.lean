module

public import CFSG.GH74.GLS.Stage2.Final.ClassicalLib
public import CFSG.GH74.GLS.Stage2.Final.ModelLayerTransport
public import CFSG.GH74.GLS.Stage1.Thm6.Prod.Resid
public import CFSG.GroupTheory.LocalCores.Layer
public import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.GH74.GLS.Stage2.Final.LayerFD

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Local

theorem odd_index_oPrimeResidual (Q : Type*) [Group Q] [Finite Q] :
    Odd (oPrimeResidual 2 Q).index := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P⟩ : Nonempty (Sylow 2 Q) := inferInstance
  have hP : (P : Subgroup Q) ≤ oPrimeResidual 2 Q := by
    intro x hx
    obtain ⟨k, hk⟩ := P.isPGroup' ⟨x, hx⟩
    refine Subgroup.subset_closure ⟨k, ?_⟩
    have := congrArg Subtype.val hk
    simpa using this
  have hdvd : (oPrimeResidual 2 Q).index ∣ (P : Subgroup Q).index := Subgroup.index_dvd_of_le hP
  have hnd : ¬ 2 ∣ (P : Subgroup Q).index := P.not_dvd_index
  exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp (fun h2 => hnd (h2.trans hdvd)))

theorem perfect_le_oPrimeResidual {Q : Type*} [Group Q] [Finite Q] {K : Subgroup Q}
    (hK : Group.IsPerfect K) : K ≤ oPrimeResidual 2 Q := by
  have : (oPrimeResidual 2 Q).Normal := CFSG.GH74.GLS.Stage1.Thm6.Prod.oPrimeResidual_normal 2 Q
  have hodd : Odd (Nat.card (Q ⧸ oPrimeResidual 2 Q)) := odd_index_oPrimeResidual Q
  have hsolv : Group.IsSolvable (Q ⧸ oPrimeResidual 2 Q) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  have himg : K.map (QuotientGroup.mk' (oPrimeResidual 2 Q)) = ⊥ := by
    by_contra hne
    have : Nontrivial ↥(K.map (QuotientGroup.mk' (oPrimeResidual 2 Q))) :=
      (Subgroup.nontrivial_iff_ne_bot _).2 hne
    have := hK
    have : Group.IsPerfect ↥(K.map (QuotientGroup.mk' (oPrimeResidual 2 Q))) :=
      Group.IsPerfect.map (QuotientGroup.mk' (oPrimeResidual 2 Q))
    exact Group.IsPerfect.not_isSolvable ↥(K.map (QuotientGroup.mk' (oPrimeResidual 2 Q))) inferInstance
  rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at himg

theorem layer_le_oPrimeResidual (Q : Type*) [Group Q] [Finite Q] : layer Q ≤ oPrimeResidual 2 Q :=
  sSup_le fun _ hK => perfect_le_oPrimeResidual hK.1.1


theorem map_layer_le_pPrimeCore (X : Type*) [Group X] [Finite X] :
    (layer X).map (QuotientGroup.mk' (pPrimeCore 2 X)) ≤ layer (X ⧸ pPrimeCore 2 X) := by
  rw [Subgroup.map_le_iff_le_comap]
  refine sSup_le fun J hJ => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  have hnot : ¬ J ≤ (QuotientGroup.mk' (pPrimeCore 2 X)).ker := by
    rw [QuotientGroup.ker_mk']
    intro hle
    have hsolv : Group.IsSolvable ↥(pPrimeCore 2 X) :=
      CFSG.FeitThompson.isSolvable_of_odd_natCard _ (Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := X)))
    have hsolvJ : Group.IsSolvable ↥J :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)
    have := CFSG.LocalCores.isQuasisimple_nontrivial hJ.1
    have := hJ.1.1
    exact Group.IsPerfect.not_isSolvable ↥J hsolvJ
  exact CFSG.LocalCores.component_le_layer
    ⟨CFSG.LocalCores.isQuasisimple_map hJ.1 _ hnot, hJ.2.map (QuotientGroup.mk'_surjective _)⟩

section Bar

variable {G : Type} [Group G]

theorem barOf_sup {z : G} {A B : Subgroup G} (hA : A ≤ Cen z) (hB : B ≤ Cen z) :
    barOf z (A ⊔ B) = barOf z A ⊔ barOf z B := by
  unfold barOf
  rw [Subgroup.subgroupOf_sup hA hB, Subgroup.map_sup]

theorem barOf_layerTimesSylow {z : G} {S : Subgroup G} (hSC : S ≤ Cen z) :
    barOf z (layerTimesSylow z S) =
      barOf z ((layer ↥(Cen z)).map (Cen z).subtype) ⊔ barOf z S :=
  barOf_sup (Subgroup.map_subtype_le _) hSC

theorem barOf_layer_le [Finite G] (z : G) :
    barOf z ((layer ↥(Cen z)).map (Cen z).subtype) ≤ layer (CentralizerBar z) := by
  have h : ((layer ↥(Cen z)).map (Cen z).subtype).subgroupOf (Cen z) = layer ↥(Cen z) :=
    Subgroup.comap_map_eq_self_of_injective (Cen z).subtype_injective _
  unfold barOf
  rw [h]
  exact map_layer_le_pPrimeCore ↥(Cen z)

end Bar

end CFSG.GH74.GLS.Stage2.Final.LayerFD

namespace CFSG.GH74.GLS.Stage2.Final

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Local


theorem layer_sup_barOf_eq_of_barOf_eq {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G}
    (hS : IsPGroup 2 ↥S) (hSC : S ≤ Cen z)
    (hB : barOf z (layerTimesSylow z S) = oPrimeResidual 2 (CentralizerBar z)) :
    layer (CentralizerBar z) ⊔ barOf z S = oPrimeResidual 2 (CentralizerBar z) := by
  apply le_antisymm
  · exact sup_le (LayerFD.layer_le_oPrimeResidual _) (barOf_le_oPrimeResidual hS)
  · rw [← hB, LayerFD.barOf_layerTimesSylow hSC]
    exact sup_le_sup_right (LayerFD.barOf_layer_le z) _

end CFSG.GH74.GLS.Stage2.Final
