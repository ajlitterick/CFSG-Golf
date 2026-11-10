module

public import CFSG.Monster.Existence.TwoPoint.ShapeSixAssembly
public import CFSG.Monster.B.CTIB.Rank2158Final
public import CFSG.Monster.B.CTIB.DistThreeProductFinal

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Monster CFSG.Monster.B CFSG.Monster.GMS CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8 CFSG.Monster.B.TwoA.Amalgam
open scoped commutatorElement

theorem exists_conj_clabelS
    (v : CVert) :
    ∃ g : Shat, ((clabelS v : Shat) : Dfull) = (g : Dfull)⁻¹ * cQ * g := by
  obtain ⟨g, rfl⟩ := cvOf_surjective v
  exact ⟨g, by rw [coe_clabelS, clabel_cvOf]⟩

theorem exists_shapeSix_MGriess
    (hcard : Nat.card MGriess = CFSG.Open.monsterOrder)
    (hT3 : BabyTableIII) {b z u : MGriess} (hV : TableV tGriess b z u) :
    ∃ y, y ∈ tableVIISet tGriess xGriess tGriess .four_B ∧
      TwoPointShape (cent2 tGriess y) 6 := by
  obtain ⟨⟨v, w, hvw, -⟩, -⟩ := CTIB.native_rank_2158_distance_three_product_final
  obtain ⟨-, -, hne, hcomm⟩ := labelsInput_of_ambient ambientRootOrbitsHyp v w hvw
  obtain ⟨-, -, hRC, hrel, -, hCcard, -, -, hFcard, hcomp, -⟩ :=
    CTIB.distance_three_product_full_centralizer_final hvw
      (R := Subgroup.centralizer {clabelS v, clabelS w})
      (F := ⁅Subgroup.centralizer {clabelS v, clabelS w},
        Subgroup.centralizer {clabelS v, clabelS w}⁆)
      (C := Subgroup.centralizer {clabelS v * clabelS w}) rfl rfl rfl
  obtain ⟨F', hF'comp, hF'uniq, -, hF'ad, -⟩ := CTIB.distThreeProduct_of_pair hvw
    (R := Subgroup.centralizer {clabelS v, clabelS w})
    (F := ⁅Subgroup.centralizer {clabelS v, clabelS w},
      Subgroup.centralizer {clabelS v, clabelS w}⁆)
    (C := Subgroup.centralizer {clabelS v * clabelS w}) rfl rfl rfl
  exact exists_shapeSix_of_product_data hcard hT3 hV (exists_conj_clabelS v)
    (exists_conj_clabelS w) hcomm.symm.eq hne.symm rfl rfl rfl hRC hrel hCcard hFcard hcomp
    ⟨F', hF'comp, hF'uniq, hF'ad⟩

end CFSG.Monster.Existence
