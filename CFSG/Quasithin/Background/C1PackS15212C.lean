module

public import CFSG.Quasithin.Background.C1PackS15212B
public import CFSG.Quasithin.Background.C1PackS15212Six
public import CFSG.Quasithin.EmptyFaithful.S141Statements

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace C1Pack12

variable {G : Type} [Group G] [Finite G]


theorem le_centralizer_of_cases {T Mc M H : Subgroup G} (hs : Setting152 T Mc M)
    (h1416 : StageLemma1416) (c19 : Lemma1519Concl T Mc M) (hH : IsHStar T M H)
    (hcases : conjClosure (oTwoUpper H) Mc = oTwoUpper H ∨
      Case15212ii T Mc (conjClosure (oTwoUpper H) Mc) ∨
      Case15212iii T Mc (conjClosure (oTwoUpper H) Mc) ∨
      Case15212He T Mc (conjClosure (oTwoUpper H) Mc)) :
    conjClosure (oTwoUpper H) Mc ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
  have hMc : perfectCore Mc ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) :=
    ((h1416 G T Mc hs.qtfe).2.2.2 Mc
      ⟨hs.qtfe.t_le_mc, pCoreOf_ne_bot_of_isTwoLocal hs.qtfe.mc_max.1⟩).1
  have hcomp : ∀ L ∈ cComp Mc, L ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) :=
    fun L hL => (le_perfectCore_of_perfect (le_of_mem_cComp hL) (perfect_of_mem_cComp hL)).trans hMc
  rcases hcases with h | h | h | h
  · rw [h]
    exact (oTwoUpper_le H).trans (c19.three H hH).1
  · exact hcomp _ h.2.1
  · obtain ⟨L, t, -, hL, htT, -, hKc, -, -⟩ := h
    rw [hKc]
    refine sup_le (hcomp L hL) fun x hx => ?_
    obtain ⟨y, hy, rfl⟩ := hx
    have htMc : t ∈ Mc := hs.qtfe.t_le_mc htT
    have hy' : y ∈ perfectCore Mc :=
      le_perfectCore_of_perfect (le_of_mem_cComp hL) (perfect_of_mem_cComp hL) hy
    have h4 : (MulAut.conj t).toMonoidHom y ∈ perfectCore Mc :=
      (Subgroup.mem_normalizer_iff.mp
        (normalizer_le_normalizer_perfectCore Mc (Subgroup.le_normalizer htMc)) y).mp hy'
    exact hMc h4
  · exact hcomp _ h.2.1


end C1Pack12

end CFSG.Quasithin
