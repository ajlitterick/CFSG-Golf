
module

public import CFSG.Quasithin.Background.C1GNC128

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace C1GN

section Statements

variable {G : Type} [Group G] [Finite G]


end Statements

section Theorem

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem le_cgsIn_of_isGNChoice {C₁ C₂ : Subgroup G → Subgroup G} (hC : IsGNChoice C₁ C₂)
    {X T : Subgroup G} (hT : IsPGroup 2 T) (hT0 : T ≠ ⊥) :
    (X ⊓ Subgroup.centralizer (C₁ T : Set G)) ⊔ (X ⊓ Subgroup.normalizer (C₂ T : Set G)) ≤
      cgsIn X T := by
  obtain ⟨h1ne, h1Z, h1char, h2ne, h2B, h2char, -⟩ := hC.pair T hT hT0
  have h1T : C₁ T ≤ T := h1Z.trans (omegaOneCenterOf_le_self T)
  have h2T : C₂ T ≤ T := h2B.trans (baum_le T)
  have h2charT : ((C₂ T).subgroupOf T).Characteristic :=
    characteristic_subgroupOf_trans (baum_le T) h2B (characteristic_baum T) h2char
  refine sup_le ?_ ?_
  · refine le_trans (inf_le_inf_left X (Subgroup.centralizer_le_normalizer _)) ?_
    exact le_iSup_of_le (C₁ T) (le_iSup_of_le h1T (le_iSup_of_le h1ne
      (le_iSup_of_le h1char le_rfl)))
  · exact le_iSup_of_le (C₂ T) (le_iSup_of_le h2T (le_iSup_of_le h2ne
      (le_iSup_of_le h2charT le_rfl)))


end Theorem

end C1GN

end CFSG.Quasithin
