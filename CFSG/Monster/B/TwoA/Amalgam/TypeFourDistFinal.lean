module

public import CFSG.Monster.B.TwoA.Amalgam.RankFiveMatrix
public import CFSG.Monster.B.TwoA.Amalgam.GlobalTypeFinal

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA


theorem native_rank_five_exact_neighbor_matrix :
    (∀ v w : CVert, ∃! i, w ∈ (![{v}, cgraph.neighborSet v, sphereThree v, sphereFour v,
      sphereDistThree v] : Fin 5 → Set CVert) i) ∧
    (∀ (v : CVert) (i : Fin 5), ∀ w ∈ (![{v}, cgraph.neighborSet v, sphereThree v, sphereFour v,
      sphereDistThree v] : Fin 5 → Set CVert) i,
      vStabOrbit v w = (![{v}, cgraph.neighborSet v, sphereThree v, sphereFour v,
        sphereDistThree v] : Fin 5 → Set CVert) i) ∧
    ∀ (v : CVert) (i j : Fin 5), ∀ w ∈ (![{v}, cgraph.neighborSet v, sphereThree v, sphereFour v,
      sphereDistThree v] : Fin 5 → Set CVert) i,
      (cgraph.neighborSet w ∩ (![{v}, cgraph.neighborSet v, sphereThree v, sphereFour v,
        sphereDistThree v] : Fin 5 → Set CVert) j).ncard =
        (!![0, 3968055, 0, 0, 0; 1, 46134, 2097152, 1824768, 0; 0, 3510, 837135, 3127410, 0;
          0, 648, 663552, 3295791, 8064; 0, 0, 0, 3898440, 69615] : Matrix (Fin 5) (Fin 5) ℕ)
          i j :=
  native_rank_five_exact_neighbor_matrix_of_ambient ambientRootOrbitsHyp

end CFSG.Monster.B.TwoA.Amalgam
