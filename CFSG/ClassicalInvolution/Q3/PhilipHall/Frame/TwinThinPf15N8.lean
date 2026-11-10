module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf14Aut
public import CFSG.ClassicalInvolution.Q3.TL3T51A

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf8

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

theorem aeAut_eight : AEAut 8 := by
  intro H hH σ hσ hperm
  subst hH
  let β : MulAut ↥(Hn 8) := MulEquiv.ofBijective σ hσ
  obtain ⟨x, hx⟩ := CFSG.ClassicalInvolution.Q3.TC.Thin.model117At_eight β (fun α h b => by
    obtain ⟨β', hβ', c', hm⟩ := hperm α h b
    refine ⟨β', hβ', c', ?_⟩
    have hle : ((memBar α h b).subgroupOf (Hn 8)).map β.toMonoidHom ≤
        (memBar β' hβ' c').subgroupOf (Hn 8) := by
      rintro _ ⟨y, hy, rfl⟩
      exact Subgroup.mem_subgroupOf.mpr (hm y (Subgroup.mem_subgroupOf.mp hy))
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    have e1 := natCard_subgroupOf_memBar' (by norm_num) β' hβ' c'
    have e2 := natCard_map_subgroupOf' (by norm_num) σ hσ.1 α h b
    exact (e1.trans e2.symm).le)
  obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective (piSub 8) x
  exact ⟨w, hx⟩


end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf8
