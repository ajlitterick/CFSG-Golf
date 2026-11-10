module

public import CFSG.Quasithin.EmptyFaithful.S146C5
public import CFSG.Quasithin.EmptyFaithful.S146R7

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

theorem stage146FRank_of (h5 : Stage1461Five) : Stage146FRank := by
  intro G _ _ T M S hB K U₁ U₂ s u hd
  refine ⟨?_, S.four_le_mIdx_of_bdata h5 hB hd⟩
  have hG : IsHTM T M (mcOf T) := S.isHTM_mcOf
  obtain ⟨-, hL3, hKeq, -⟩ := hd.c24
  have hKn : mcOf T ≤ Subgroup.normalizer (K : Set G) := by
    rw [hKeq]
    exact Subgroup.le_normalizer.trans (normalizer_le_normalizer_perfectCore _)
  exact four_lt_relIndex_of_kbarIsL3Two
    (isSylowTwoOf_of_quasithinIsSylowTwo S.hyp.sylow hG.1.1) (le_of_mem_cComp hd.hK) hKn hL3


end CFSG.Quasithin
