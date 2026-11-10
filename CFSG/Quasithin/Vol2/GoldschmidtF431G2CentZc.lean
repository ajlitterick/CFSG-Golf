module

public import CFSG.Quasithin.Vol2.GoldschmidtF431G2CentZ
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsModG2Ctr

public noncomputable section

namespace CFSG.Quasithin.H13.F431.G2.Cent

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Quasithin
  CFSG.QuasithinUnique.Vol2Native.L239.Lie.G2

set_option linter.unusedSectionVars false

variable {K : Type} [Field K] [CharP K 2] [Finite K]


theorem centerOf_perfectCore_Pr_le_Xc {f : ℕ} (hf : 2 ≤ f) (hK : Nat.card K = 2 ^ f) :
    centerOf (perfectCore (Pr K)) ≤ Xc K := by
  intro x hx
  have hPC : parabolicSubgroup Tag.G2 K {i1} ≤ adjointGroup Tag.G2 K :=
    parabolicSubgroup_le_adjointGroup Tag.G2 K {i1}
  obtain ⟨hx1, hx2⟩ :=
    (CFSG.Quasithin.H13.Sec53F.G2.mem_centerOf_perfectCore_subgroupOf hPC x).1 hx
  obtain ⟨s, hs⟩ := CFSG.Quasithin.H13.Sec53F.G2.center_one hK hf hx1 hx2
  exact ⟨s, Subtype.ext hs.symm⟩

theorem centerOf_perfectCore_Pr_eq {f : ℕ} (hf : 2 ≤ f) (hK : Nat.card K = 2 ^ f) :
    centerOf (perfectCore (Pr K)) = Xc K :=
  le_antisymm (centerOf_perfectCore_Pr_le_Xc hf hK)
    (Xc_le_centerOf_perfectCore_Pr (CFSG.Quasithin.H13.Sec53F.G2.four_le_card_of hK hf))


end CFSG.Quasithin.H13.F431.G2.Cent
