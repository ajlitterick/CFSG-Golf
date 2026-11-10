module

public import CFSG.Quasithin.Background.E2Two
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.Blocks
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.E6Gamma

public section

open scoped Pointwise commutatorElement

namespace CFSG.Quasithin.RonanE611

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E3 CFSG.Quasithin.E1 CFSG.QuasithinUnique

@[expose] def rootGroupOfParabolicR {Y : Type*} [Group Y] (P : Subgroup Y) : Subgroup Y :=
  Subgroup.closure {x : Y | x ∈ P ∧ ∃ k : ℕ, x ^ 2 ^ k = 1} ⊓
    Subgroup.centralizer
      (Subgroup.closure {x : Y | x ∈ P ∧ ∃ k : ℕ, x ^ 2 ^ k = 1} : Set Y)


end CFSG.Quasithin.RonanE611
