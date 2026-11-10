module

public import CFSG.Quasithin.Background.S1567V2
public import CFSG.Quasithin.Background.S1567Z5

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement Pointwise

namespace S1567

section MS

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ E : Subgroup G} {t s : G}

theorem false_of_twoLocal_ge (h11 : StageLemma14111) (h113 : StageLemma14113)
    (k : Ctx67 G T Mc M V₁ V₂ E t) (r67 : Res15367 T Mc M V₁ V₂ E) (gl : GoldLine153 T V₁ E s)
    {A : Subgroup G} (hAne : A ≠ ⊥) (hApg : IsPGroup 2 ↥A)
    (hTn : T ≤ Subgroup.normalizer (A : Set G)) (hXEn : XE153 E ≤ Subgroup.normalizer (A : Set G))
    (hYFn : YF153 Mc M E s ≤ Subgroup.normalizer (A : Set G)) : False := by
  have hloc : IsTwoLocal (Subgroup.normalizer (A : Set G)) := ⟨A, hAne, hApg, rfl⟩
  obtain ⟨M', hM', hle⟩ := exists_maxTwoLocal_ge hloc
  have hInM : InM T M' := ⟨hM', hTn.trans hle⟩
  rcases (k.c.hyp.lemma_15_3_2_three h11).mp hInM with rfl | rfl
  · exact r67.XE_not_le (fun x hx => hle (hXEn hx))
  · exact YF_not_le_Mc h11 h113 k gl (fun y hy => hle (hYFn hy))

theorem not_normal_char_TE (h11 : StageLemma14111) (h113 : StageLemma14113)
    (k : Ctx67 G T Mc M V₁ V₂ E t) (r67 : Res15367 T Mc M V₁ V₂ E) (gl : GoldLine153 T V₁ E s)
    {C : Subgroup G} (hCT : C ≤ TE153 T E) (hC1 : C ≠ ⊥)
    (hchar : (C.subgroupOf (TE153 T E)).Characteristic)
    (hCG : G0_153 T Mc M E s ≤ Subgroup.normalizer (C : Set G)) : False := by
  have hCp : IsPGroup 2 ↥C := k.c.hyp.qtfe.sylow.1.to_le (hCT.trans inf_le_left)
  have hTn : T ≤ Subgroup.normalizer (C : Set G) :=
    (T_le_normalizer_TE k.r66).trans
      (normalizer_le_normalizer_of_characteristic_subgroupOf hCT hchar)
  refine false_of_twoLocal_ge h11 h113 k r67 gl hC1 hCp hTn ?_ ?_
  · exact fun _ hx => hCG (Subgroup.mem_sup_right (Subgroup.mem_sup_left hx))
  · exact fun _ hy => hCG (Subgroup.mem_sup_left (Subgroup.mem_sup_left hy))

theorem centralizer_pCore_G0_le (k : Ctx67 G T Mc M V₁ V₂ E t) (r67 : Res15367 T Mc M V₁ V₂ E)
    (r68 : Res15368NoTwo T Mc M E s) :
    G0_153 T Mc M E s ⊓ Subgroup.centralizer (pCoreOf 2 (G0_153 T Mc M E s) : Set G) ≤
      pCoreOf 2 (G0_153 T Mc M E s) := fun _ hx =>
  centralizer_V0_inf_G0_le_pCore k r67
    ⟨hx.1, Subgroup.centralizer_le (V0_le_pCore_NT r68) hx.2⟩


theorem isSQTKIn_G0 (c : Ctx153 G T Mc M V₁ V₂ t) (r68 : Res15368NoTwo T Mc M E s) :
    IsSQTKIn (G0_153 T Mc M E s) := sqtkGroup_G0_NT c r68

theorem charTwo_G0 (k : Ctx67 G T Mc M V₁ V₂ E t) (r67 : Res15367 T Mc M V₁ V₂ E)
    (r68 : Res15368NoTwo T Mc M E s) : CharTwo (G0_153 T Mc M E s) :=
  centralizer_pCore_G0_le k r67 r68

theorem ms2_G0 (k : Ctx67 G T Mc M V₁ V₂ E t) (r67 : Res15367 T Mc M V₁ V₂ E)
    (gl : GoldLine153 T V₁ E s) (r68 : Res15368NoTwo T Mc M E s) :
    ∃ H' : Subgroup G, H' < G0_153 T Mc M E s ∧ ¬ 2 ∣ H'.relIndex (G0_153 T Mc M E s) ∧
      TE153 T E = pCoreOf 2 H' := by
  have hSyl := isSylowTwoOf_TE_G0_NT k.c k.L k.r66 r67 gl r68
  have hSG : TE153 T E ≤ G0_153 T Mc M E s := hSyl.1
  have hp : IsPGroup 2 ↥(TE153 T E) := k.c.hyp.qtfe.sylow.1.to_le inf_le_left
  refine ⟨TE153 T E, lt_of_le_of_ne hSG ?_, hSyl.2.2, ?_⟩
  · intro h
    refine r67.XE_not_le (fun x hx => ?_)
    have hxG : x ∈ G0_153 T Mc M E s := Subgroup.mem_sup_right (Subgroup.mem_sup_left hx)
    rw [← h] at hxG
    exact k.c.hyp.T_le hxG.1
  · exact le_antisymm (le_pCoreOf_of_le_normalizer 2 le_rfl Subgroup.le_normalizer hp)
      (pCoreOf_le 2 _)

theorem ms3_G0 (h11 : StageLemma14111) (h113 : StageLemma14113) (k : Ctx67 G T Mc M V₁ V₂ E t)
    (r67 : Res15367 T Mc M V₁ V₂ E) (gl : GoldLine153 T V₁ E s) :
    ∀ C : Subgroup G, C ≤ TE153 T E → C ≠ ⊥ → (C.subgroupOf (TE153 T E)).Characteristic →
      ¬ G0_153 T Mc M E s ≤ Subgroup.normalizer (C : Set G) :=
  fun _ hCT hC1 hchar hCG => not_normal_char_TE h11 h113 k r67 gl hCT hC1 hchar hCG

theorem isMSPair_G0_TE_of_exists_L (h11 : StageLemma14111) (h113 : StageLemma14113)
    (k : Ctx67 G T Mc M V₁ V₂ E t) (r67 : Res15367 T Mc M V₁ V₂ E) (gl : GoldLine153 T V₁ E s)
    (r68 : Res15368NoTwo T Mc M E s)
    (hL : ∃ L : Subgroup G, L ∈ cComp (G0_153 T Mc M E s) ∧
      ((G0_153 T Mc M E s : Subgroup G) : Set G) = (L : Set G) * (TE153 T E : Set G) ∧
      IsRankTwoLie2Derived ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L))) :
    IsMSPair (G0_153 T Mc M E s) (TE153 T E) :=
  ⟨⟨isSQTKIn_G0 k.c r68, charTwo_G0 k r67 r68, hL⟩, Or.inl (ms2_G0 k r67 gl r68),
    ms3_G0 h11 h113 k r67 gl⟩

end MS

end S1567


end CFSG.Quasithin
