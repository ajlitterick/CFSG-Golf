module

public import CFSG.LocalAnalysis.ComponentClassification.BFailureLocalization
public import CFSG.LocalAnalysis.ComponentClassification.BadSolvableQuotients

public section

namespace CFSG.ComponentClassification.CatalogueRelativeB


@[expose] def normalFixedEquivalence {G : Type*} [Group G]
    (N : Subgroup G) (t : G) :
    N.subgroupOf (Subgroup.centralizer ({t} : Set G)) ≃*
      (Subgroup.centralizer ({t} : Set G)).subgroupOf N where
  toFun x := ⟨⟨x.val.val, x.property⟩, x.val.property⟩
  invFun x := ⟨⟨x.val.val, x.property⟩, x.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem involution_centralizer_twoComponent_quasisimple {G : Type*} [Group G] [Finite G]
    (N : Subgroup G) [N.Normal] [Group.IsSolvable (G ⧸ N)]
    (t : G)
    (hfixed : ∀ L : Subgroup ((Subgroup.centralizer ({t} : Set G)).subgroupOf N),
      TwoComponents.IsTwoComponent L → CFSG.Open.IsQuasisimple L)
    (L : Subgroup (Subgroup.centralizer ({t} : Set G)))
    (hL : TwoComponents.IsTwoComponent L) : CFSG.Open.IsQuasisimple L := by
  let centralizer := Subgroup.centralizer ({t} : Set G)
  let projection := (QuotientGroup.mk' N).domRestrict centralizer
  have hkernel : projection.ker = N.subgroupOf centralizer := by
    rw [MonoidHom.ker_domRestrict, QuotientGroup.ker_mk']
  have hle : L ≤ N.subgroupOf centralizer := by
    have hcontained := BadSolvableQuotients.component_le_kernel projection L hL
    rwa [hkernel] at hcontained
  let equivalence := normalFixedEquivalence N t
  have hrestricted := TwoComponentTransport.of_overgroup hL hle
  have htransport := (TwoComponentTransport.equiv_iff equivalence (L.subgroupOf _)).mpr
    hrestricted
  have hquasisimple := hfixed _ htransport
  let subgroupEquivalence :=
    (Subgroup.subgroupOfEquivOfLe hle).symm.trans
      ((L.subgroupOf _).equivMapOfInjective equivalence.toMonoidHom equivalence.injective)
  exact Components.quasisimple_of_equiv subgroupEquivalence hquasisimple

theorem involution_centralizer_bad_eq_bot {G : Type*} [Group G] [Finite G]
    (N : Subgroup G) [N.Normal] [Group.IsSolvable (G ⧸ N)]
    (t : G)
    (hfixed : ∀ L : Subgroup ((Subgroup.centralizer ({t} : Set G)).subgroupOf N),
      TwoComponents.IsTwoComponent L → CFSG.Open.IsQuasisimple L) :
    TwoComponents.badSubgroup (Subgroup.centralizer ({t} : Set G)) = ⊥ := by
  apply le_antisymm _ bot_le
  apply sSup_le
  intro L hbad
  exact (hbad.2 (involution_centralizer_twoComponent_quasisimple N t hfixed L hbad.1)).elim

theorem local_bad_eq_bot_of_normal_fixed_components {G : Type*} [Group G] [Finite G]
    (N : Subgroup G) [N.Normal] [Group.IsSolvable (G ⧸ N)]
    (hoddCenter : Odd (Nat.card (Subgroup.center G)))
    (hproper : ∀ X : Subgroup G, X ≠ ⊤ → CentralTwoBInclusion.Property X)
    (hfixed : ∀ t : G, orderOf t = 2 →
      ∀ L : Subgroup ((Subgroup.centralizer ({t} : Set G)).subgroupOf N),
        TwoComponents.IsTwoComponent L → CFSG.Open.IsQuasisimple L)
    (S : Subgroup G) (hne : S ≠ ⊥) (htwo : IsPGroup 2 S) :
    TwoComponents.badSubgroup (Subgroup.normalizer (S : Set G)) = ⊥ := by
  obtain ⟨z, hz, hmem, hcentral⟩ :=
    BFailureLocalization.exists_central_involution S htwo hne
  have hcentralizerProper :=
    BFailureLocalization.centralizer_proper_of_odd_center hoddCenter z hz
  have hbound := BFailureLocalization.bad_normalizer_le_centralizer S htwo hne z hmem
    hcentral (hproper _ hcentralizerProper)
  have hcentralizerBot := involution_centralizer_bad_eq_bot N z (hfixed z hz)
  rw [hcentralizerBot, Subgroup.map_bot] at hbound
  have hmapBot := le_antisymm hbound bot_le
  apply (Subgroup.map_eq_bot_iff _).mp at hmapBot
  rw [(MonoidHom.ker_eq_bot_iff _).mpr
    (Subgroup.normalizer (S : Set G)).subtype_injective] at hmapBot
  exact le_antisymm hmapBot bot_le


end CFSG.ComponentClassification.CatalogueRelativeB
