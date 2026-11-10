module

public import CFSG.Quasithin.EmptyFaithful.S151Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

theorem lemma_15_1_1_one {T Mc M : Subgroup G} (h : quasithinQTFE14Cat G T Mc) (hM : IsMf T Mc M)
    {H : Subgroup G} (hH : IsHStar T M H) :
    Hyp315Base T M (M ⊓ Subgroup.normalizer
      ((T ⊓ Subgroup.centralizer (VZ T M : Set G) : Subgroup G) : Set G)) H (VZ T M) ∧
      Hyp315.CaseII M H (VZ T M) := by
  obtain ⟨S, rfl⟩ := h.exists_sylow
  have hmax : IsOrdMaximalIn (S : Subgroup G) (InM (S : Subgroup G)) M := hM.1
  obtain ⟨⟨hpc, -⟩, hred, -, -⟩ := A57.main h.qtke.2.1 S hmax (Or.inl rfl)
  have hSM : (S : Subgroup G) ≤ M := hM.1.1.2
  have hVn := le_normalizer_VZ (S : Subgroup G) M
  exact ⟨⟨le_inf hSM (le_normalizer_inf_centralizer' Subgroup.le_normalizer (hSM.trans hVn)),
    inf_le_left, hH, hred, hpc⟩, inf_le_right.trans hVn⟩


end CFSG.Quasithin
