module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.Quasithin.SteinbergBS

open Subgroup

variable {G : Type*} [Group G]

theorem le_pCore_of_normal {p : ℕ} {K : Subgroup G} {Q : Subgroup K} [Q.Normal]
    (hQ : IsPGroup p Q) : Q ≤ pCore p K :=
  le_sSup ⟨inferInstance, hQ⟩


end CFSG.Quasithin.SteinbergBS
