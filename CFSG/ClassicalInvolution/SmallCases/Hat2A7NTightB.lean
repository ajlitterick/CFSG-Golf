module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7NTightA

public section

namespace CFSG.ClassicalInvolution.Hat2A7N

open CFSG.Open CFSG.ClassicalInvolution.Hat2A7

section Clique

variable {F : Type} [Group F] [Finite F] {K : Subgroup F} {z : F}

omit [Finite F] in
theorem TightSettingN.rebase (S : TightSettingN F K z) {x : F} (hx : x ∈ classOf z) :
    TightSettingN F (memb K z x) x := by
  have hc : IsConjSubgroup K (memb K z x) := S.isConjSubgroup_memb hx
  refine ⟨S.tight.memb hx, S.center_trivial, ?_, ?_⟩
  · intro y hy2 hyE L M u v hL hM hLc hMc
    refine S.IH y hy2 ((IsCommProd.congr hx).mp hyE) L M u v ?_ (hc.trans hM) hLc hMc
    rcases hL with hL | hL
    · exact Or.inl (hc.trans hL)
    · exact Or.inr (IsTwinDiag.of_isConjSubgroup hc hL)
  · intro L u hL hLc
    exact S.P1 L u (hc.trans hL) hLc


omit [Finite F] in
theorem TightSettingN.cliqueSub_le_normalizer (S : TightSettingN F K z) {v : F}
    (hv : v ∈ Zset K z) : cliqueSub K z ≤ Subgroup.normalizer (memb K z v : Set F) := by
  refine iSup₂_le fun w hw => ?_
  rcases S.commOrEq_of_mem_Zset hw hv with h | h
  · rw [h]
    exact Subgroup.le_normalizer
  · intro g hg
    have hc : g ∈ Subgroup.centralizer ((memb K z v : Subgroup F) : Set F) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact (h g hg x hx).symm
    exact Subgroup.centralizer_le_normalizer ((memb K z v : Subgroup F) : Set F) hc


end Clique

section Swap


end Swap

end CFSG.ClassicalInvolution.Hat2A7N
