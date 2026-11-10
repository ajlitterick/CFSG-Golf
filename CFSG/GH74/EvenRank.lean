module

import CFSG.GroupTheory.LocalCores.Layer
import CFSG.LocalAnalysis.ComponentInitial.LocalComponents
import CFSG.LocalAnalysis.PreuniquenessRankFour.GeneratorRank
import CFSG.LocalAnalysis.QuasithinUnique.CharTwoTransport
public import CFSG.GH74.Defs
public import CFSG.LocalAnalysis.SectionRank.SQT
import CFSG.LocalAnalysis.SectionRank.SubgroupRank

public section

namespace CFSG.GH74

open Subgroup

theorem inf_centralizer_map_subtype_le_iff {G : Type*} [Group G] (H : Subgroup G)
    (Q : Subgroup H) :
    H ⊓ centralizer ((Q.map H.subtype : Subgroup G) : Set G) ≤ Q.map H.subtype ↔
      centralizer (Q : Set H) ≤ Q := by
  constructor
  · intro h x hx
    have hx' : (x : G) ∈ H ⊓ centralizer ((Q.map H.subtype : Subgroup G) : Set G) := by
      refine ⟨x.2, mem_centralizer_iff.2 ?_⟩
      rintro _ ⟨y, hy, rfl⟩
      exact congrArg Subtype.val (mem_centralizer_iff.1 hx y hy)
    obtain ⟨y, hy, hyx⟩ := h hx'
    exact (Subtype.ext hyx : y = x) ▸ hy
  · intro h x hx
    obtain ⟨hxH, hxc⟩ := hx
    have hx' : (⟨x, hxH⟩ : H) ∈ centralizer (Q : Set H) := by
      refine mem_centralizer_iff.2 fun y hy => Subtype.ext ?_
      exact mem_centralizer_iff.1 hxc _ ⟨y, hy, rfl⟩
    exact ⟨⟨x, hxH⟩, h hx', rfl⟩

theorem isCharTwoType_iff {G : Type*} [Group G] :
    CFSG.Assembly.IsCharTwoType G ↔ CFSG.IsCharacteristicPType G 2 :=
  CFSG.Assembly.isCharTwoType_iff_isCharacteristicPType

theorem SectionalTwoRankLE.rank_le_of_isPGroup {X : Type*} [Group X] [Finite X] {r : ℕ}
    (h : SectionalTwoRankLE X r) {P : Subgroup X} (hP : IsPGroup 2 P) : Group.rank P ≤ r := by
  obtain ⟨s, hs, hsP⟩ := h P hP
  exact (Subgroup.rank_congr hsP.symm).le.trans
    ((Subgroup.rank_closure_finset_le_card s).trans hs)

theorem Gen4.rank_le_four {X : Type*} [Group X] [Finite X] (h : Gen4 X) {P : Subgroup X}
    (hP : IsPGroup 2 P) : Group.rank P ≤ 4 :=
  SectionalTwoRankLE.rank_le_of_isPGroup h hP


open CFSG.PreuniquenessRankFour.Helpers in
theorem two_mul_pRank_le_rank_pCoreOf {G : Type*} [Group G] [Finite G]
    (hchar : CFSG.Assembly.IsCharTwoType G) {H : Subgroup G} (hH : CFSG.Assembly.IsTwoLocal H)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    2 * CFSG.Assembly.pRank p H ≤ Group.rank (CFSG.Assembly.pCoreOf 2 H) := by
  let : IsMulCommutative (CFSG.Open.pCoreOf 2 H ⧸ frattini (CFSG.Open.pCoreOf 2 H)) :=
    pGroup_frattini_quotient_isMulCommutative 2 (pCoreOf_isPGroup 2 H)
  let : CommGroup (CFSG.Open.pCoreOf 2 H ⧸ frattini (CFSG.Open.pCoreOf 2 H)) :=
    IsMulCommutative.instCommGroup
  let := pGroup_binary_frattini_quotient_module (pCoreOf_isPGroup 2 H)
  have hdim := local_twoCore_frattini_dimension_bound p hp hp2 hchar H hH
  rw [twoGroup_frattini_finrank_eq_group_rank (pCoreOf_isPGroup 2 H)] at hdim
  exact hdim

open CFSG.PreuniquenessRankFour.Helpers in
theorem pRank_le_two_of_charTwoType_gen4 {G : Type*} [Group G] [Finite G]
    (hchar : CFSG.Assembly.IsCharTwoType G) (hgen : Gen4 G) {H : Subgroup G}
    (hH : CFSG.Assembly.IsTwoLocal H) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    CFSG.Assembly.pRank p H ≤ 2 := by
  have h2 := two_mul_pRank_le_rank_pCoreOf hchar hH hp hp2
  have h4 : Group.rank (CFSG.Assembly.pCoreOf 2 H) ≤ 4 :=
    hgen.rank_le_four (pCoreOf_isPGroup 2 H)
  omega

theorem evenRank_le_two_of_charTwoType_gen4 {G : Type*} [Group G] [Finite G]
    (hchar : CFSG.Assembly.IsCharTwoType G) (hgen : Gen4 G) : CFSG.Assembly.evenRank G ≤ 2 := by
  refine csSup_le' ?_
  rintro k ⟨p, H, hp, hp2, hH, rfl⟩
  exact pRank_le_two_of_charTwoType_gen4 hchar hgen hH hp hp2


private theorem oddCore_eq_pPrimeCore_two (X : Type*) [Group X] :
    CFSG.Assembly.oddCore X = pPrimeCore 2 X :=
  (ComponentClassification.AssemblyBPredicates.oddCore_eq_piCore X).trans
    (CFSG.pPrimeCore_eq_piCore X 2).symm

theorem not_isComponentType_of_layerBar_eq_bot {G : Type*} [Group G] [Finite G]
    (h : ∀ x : G, orderOf x = 2 → layerBar x = ⊥) : ¬ CFSG.Assembly.IsComponentType G := by
  rintro ⟨t, ht, L, hL⟩
  have hL' : CFSG.IsComponent L :=
    (ComponentClassification.AssemblyBPredicates.isComponentOf_top_iff_native L).1 hL
  let e := QuotientGroup.quotientMulEquivOfEq
    (oddCore_eq_pPrimeCore_two ↥(centralizer ({t} : Set G)))
  have hK : CFSG.IsComponent (L.map e.toMonoidHom) :=
    (LocalAnalysis.ComponentInitial.isComponent_map_iff e L).2 hL'
  have hle : L.map e.toMonoidHom ≤ layerBar t := LocalCores.component_le_layer hK
  rw [h t ht, le_bot_iff] at hle
  have hL0 : L = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective L (f := e.toMonoidHom) e.injective).1 hle
  have : Nontrivial L := LocalCores.isQuasisimple_nontrivial hL'.1
  exact (Subgroup.nontrivial_iff_ne_bot L).1 this hL0


end CFSG.GH74
