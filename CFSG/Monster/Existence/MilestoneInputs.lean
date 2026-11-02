module

public import CFSG.Monster.Existence.MilestoneAssembly
public import CFSG.Monster.Existence.BabyAmbient
public import CFSG.Monster.Existence.BabyW3Classes
public import CFSG.Monster.Existence.BabyW3Griess
public import CFSG.Monster.Existence.TableVGriess
public import CFSG.Monster.Existence.TableVSylow
public import CFSG.Monster.Existence.TwoPoint.ThreeIII
public import CFSG.Monster.Existence.TwoPoint.GammaTransitive
public import CFSG.Monster.Existence.TwoPoint.ThreeVAll
public import CFSG.Monster.Existence.TwoPoint.ShapeSixFinal
public import CFSG.Monster.Existence.BabyTableIVOf
public import CFSG.Monster.Existence.BabyThreeSwap
public import CFSG.Monster.Existence.TwoPoint.FourDMain
public import CFSG.Monster.Existence.OrderFourT
public import CFSG.Monster.GMS.InterfacesOf
public import CFSG.Sporadic.Presentation.Th
public import CFSG.Monster.Existence.TwoPoint.Fi23S4CommBase
public import CFSG.Monster.Existence.TwoPoint.Fi23S4ConjBase
public import CFSG.Monster.Existence.TwoPoint.Fi23S4CubeBase

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Monster.GMS CFSG.Blueprint.NativeSporadic

theorem babyTableIII :
    BabyTableIII :=
  babyTableIII_of_rep_three natCard_centralizer_rep_three

theorem babyTableIV :
    BabyTableIV :=
  babyTableIV_of babyTableIII

theorem tableV_tGriess
    (hA : IsTwoACentralizer tGriess) :
    TableV tGriess uGriess xGriess uW3 := by
  obtain ⟨φ, hφ⟩ := exists_isBabyCover_of_isTwoACentralizer orderOf_tGriess hA
  have hb : Nat.card ↥(cent2 tGriess uGriess) = tableVOrderB := by
    rw [natCard_cent2_tGriess_uGriess_of centralizerInput_B,
      CFSG.LieType.Chevalley.C2E6Std.card_stdGroup]
    norm_num [tableVOrderB]
  exact tableV_tGriess_of hφ babyTableIII (natCard_cent_tGriess_of hA) hb uW3_mem_cent
    orderOf_uW3 uW3_ne_tGriess exists_swap_uW3 natCard_cent2_tGriess_uW3 exists_sq_eq_tGriess
    (center_sylow_cent2_tGriess_xGriess natCard_cent2_tGriess_xGriess)

theorem gmsInterfaces_MGriess_of
    (hSLS : SLSStatement (phiB uBar))
    (hcls : ∀ s : MGriess, orderOf s = 2 → IsConj tGriess s ∨ IsConj xGriess s)
    (hA : IsTwoACentralizer tGriess) : GMSInterfaces (phiB uBar) MGriess :=
  GMSInterfaces.of_babyFacts hSLS (tableVIn_MGriess_of hcls (tableV_tGriess hA)) babyTableIII
    babyTableIV (babyThreeSwap_of babyTableIII)

theorem monsterExistenceStatement_MGriess_of_remaining
    (hStroth : ∀ d₀ : Blueprint.NativeSporadic.B, orderOf d₀ = 2 →
      Matrix.rank (d₀.val.val - 1) = 1860 →
      ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (d : G), orderOf d = 2 →
        Nonempty (Subgroup.centralizer ({d} : Set G) ≃*
          Subgroup.centralizer ({d₀} : Set Blueprint.NativeSporadic.B)) →
        Nonempty (G ≃* Blueprint.NativeSporadic.B))
    (hex : OddExhaustive tGriess xGriess) :
    MonsterExistenceStatement MGriess := by
  obtain ⟨⟨-, -, -, hcard⟩, -, -, -, hcls, hA, -⟩ := monster_existence_clauses_one_two_of_stroth hStroth
  have hSLS : SLSStatement (phiB uBar) :=
    hStroth (phiB uBar) orderOf_phiB_uBar rank_phiB_uBar_sub_one
  have hAt := hA _ (IsConj.refl _)
  have hTh := CFSG.Sporadic.Presentation.Th.finite_card_le
  have I := gmsInterfaces_MGriess_of hSLS hcls hAt
  have htr := gammaSet_transitive_MGriess I hex hcard hAt (hA fiBeta isConj_fiBeta) hTh
  exact monsterExistenceStatement_MGriess_of_open hStroth I hex hTh twoPointShape_one_MGriess
    (exists_shapeSix_MGriess hcard babyTableIII (tableV_tGriess hAt))
    (hiii_of_threeIIIData (threeIIIData_MGriess I hex hcard hAt hTh htr))
    (threeVData_MGriess I hex hcard hAt hTh)
    (fourD_MGriess I hex hcard hAt hTh centralizerInput_B)

end CFSG.Monster.Existence
