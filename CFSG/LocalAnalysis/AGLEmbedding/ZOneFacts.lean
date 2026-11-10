module

public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockInputs
public import CFSG.LocalAnalysis.AGLEmbedding.PhaseThreeConfig

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers

section Sylow

variable {G : Type*} [Group G] [Finite G]

theorem card_le_card_of_isSylowTwoOf {T K U : Subgroup G} (hT : IsSylowTwoOf T K) (hUK : U ≤ K)
    (hU : IsPGroup 2 U) : Nat.card U ≤ Nat.card T := by
  have hT' : IsPGroup 2 (T.subgroupOf K) := hT.2.1.comap_subtype
  have h := card_le_card_map_sylow (hT'.toSylow hT.2.2) hU hUK
  rwa [IsPGroup.toSylow_coe, Subgroup.map_subgroupOf_eq_of_le hT.1] at h

theorem isSylowTwoOf_eq_of_le {T K U : Subgroup G} (hT : IsSylowTwoOf T K) (hUK : U ≤ K)
    (hU : IsPGroup 2 U) (hTU : T ≤ U) : U = T :=
  (Subgroup.eq_of_le_of_card_ge hTU (card_le_card_of_isSylowTwoOf hT hUK hU)).symm

theorem le_of_isSylowTwoOf_of_le_normalizer {T K S : Subgroup G} (hT : IsSylowTwoOf T K)
    (hSK : S ≤ K) (hS : IsPGroup 2 S) (hKS : K ≤ Subgroup.normalizer (S : Set G)) : S ≤ T :=
  le_sup_left.trans (isSylowTwoOf_eq_of_le hT (sup_le hSK hT.1)
    (IsPGroup.to_sup_of_normal_left' hS hT.2.1 (hT.1.trans hKS)) le_sup_right).le

theorem isSylowTwoOf_of_forall_normalizer_le {T M : Subgroup G} (hTM : T ≤ M) (hT : IsPGroup 2 T)
    (h : ∀ U : Subgroup G, U ≤ M → IsPGroup 2 U → T ≤ U →
      U ≤ Subgroup.normalizer (T : Set G) → U ≤ T) :
    IsSylowTwoOf T M := by
  obtain ⟨Q, hQ⟩ := (hT.comap_subtype (K := M)).exists_le_sylow
  have hQM : (Q : Subgroup M).map M.subtype ≤ M := Subgroup.map_subtype_le _
  have hQ2 : IsPGroup 2 ((Q : Subgroup M).map M.subtype) := Q.isPGroup'.map _
  have hTQ : T ≤ (Q : Subgroup M).map M.subtype := fun x hx => ⟨⟨x, hTM hx⟩, hQ hx, rfl⟩
  have hsyl : IsSylowTwoOf ((Q : Subgroup M).map M.subtype) M := by
    refine ⟨hQM, hQ2, ?_⟩
    change ¬ 2 ∣ (Subgroup.comap M.subtype ((Q : Subgroup M).map M.subtype)).index
    rw [Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
    exact Sylow.not_dvd_index Q
  rcases eq_or_lt_of_le hTQ with heq | hlt
  · rwa [heq]
  · obtain ⟨x, hxQ, hxT, hxN⟩ := exists_mem_normalizer_not_mem_of_lt_of_isPGroup hQ2 hlt
    exact absurd (h _ (inf_le_left.trans hQM) (hQ2.to_le inf_le_left)
      (le_inf hTQ Subgroup.le_normalizer) inf_le_right ⟨hxQ, hxN⟩) hxT

omit [Finite G] in
theorem le_normalizer_omegaOneCenterOf_of_le_normalizer {T U : Subgroup G}
    (hU : U ≤ Subgroup.normalizer (T : Set G)) :
    U ≤ Subgroup.normalizer (omegaOneCenterOf T : Set G) := by
  have := QuasithinUnique.Setup.characteristic_omegaOneCenterOf T
  have h := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
    ((omegaOneCenterOf T).subgroupOf T)
  rw [Subgroup.map_subgroupOf_eq_of_le (QuasithinUnique.Setup.omegaOneCenterOf_le T)] at h
  exact hU.trans h


end Sylow

section Escape


end Escape

section PhaseThree


end PhaseThree

end CFSG.AGLEmbedding
