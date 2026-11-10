module

public import CFSG.Sporadic.Schreier.Co3Faithful
public import CFSG.Sporadic.Schreier.Co3OrderCheck
public import CFSG.Certificates.NativeSchreierCard
public import CFSG.Sporadic.Schreier.Co3ChainUtil

public noncomputable section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.Schreier.Co3

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.Schreier.Co3.Native

theorem co3ChainArrays :
    ChainArrays co3Chain (co3ChainArrs.extract 0 co3ChainGenCount)
    co3ChainArrs co3ChainBaseArr
    (wordsArr co3ChainGenCount co3ChainStrongCount co3ChainDerivations) :=
  chainArrays_ofArrays co3ChainArrs_inv


theorem co3Chain_valid :
    ValidSchreier co3Chain ∧ ∀ i : Fin co3Chain.baseCount,
    co3Chain.orbitSize i = ((rawLevels 276 co3ChainArrs co3ChainBaseArr)[(i : ℕ)]!).pts.size :=
  validSchreier_of_chainOK co3ChainArrays (by norm_num) co3Order_check.1


theorem card_co3P :
    Nat.card co3P = 495766656000 := by
  rw [co3P, card_originalSubgroup_of_chainOK co3ChainArrays (by norm_num) co3Order_check.1,
    co3Order_check.2.1]
  rfl


theorem co3GenPerm_mem (k : ℕ) (hk : k < 2) : co3GenPerm k ∈ co3P := by
  rw [co3P_eq]
  exact Subgroup.subset_closure ⟨⟨k, hk⟩, rfl⟩


theorem card_Co3_of_perm :
    Nat.card Blueprint.NativeSporadic.Co3 = 495766656000 := by
  rw [Nat.card_congr co3PermEquiv.toEquiv, card_co3P]


end CFSG.Sporadic.Schreier.Co3
