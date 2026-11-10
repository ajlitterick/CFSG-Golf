module

public import CFSG.Sporadic.HNOddCore.AlmostSimple

public noncomputable section

namespace CFSG.Sporadic.HNOddCore

open CFSG.Sporadic.HNSchreier CFSG.Sporadic.FischerOddCore

theorem center_bot_of_mulEquiv_sub {G G0 : Type*} [Group G] [Group G0] {J : Subgroup G0}
    (e : G ≃* J) (h : Subgroup.center J = ⊥) : Subgroup.center G = ⊥ :=
  center_eq_bot_of_mulEquiv e h

theorem ctuc_hn_generalized_fitting_involution_centralizer_odd_core_trivial
    {X : Type*}
    [Group X] [Finite X] (_hF : IsSimpleGroup (CFSG.generalizedFitting X))
    (hJ : Nonempty (CFSG.generalizedFitting X ≃* Blueprint.NativeSporadic.HN)) :
    ((CFSG.generalizedFitting X).index = 1 ∨ (CFSG.generalizedFitting X).index = 2) ∧
      ∀ t : X, orderOf t = 2 → CFSG.oddCore ↥(Subgroup.centralizer ({t} : Set X)) = ⊥ := by
  have : (CFSG.generalizedFitting X).Normal :=
    (CFSG.LocalCores.generalized_fitting_characteristic (G := X)).2
  have hZ : Subgroup.center (CFSG.generalizedFitting X) = ⊥ :=
    center_bot_of_mulEquiv_sub (hJ.some.trans hnEquivJ) center_JH
  exact ctuc_hn_almost_simple_involution_centralizer_odd_core_trivial _ hJ
    (centralizer_generalizedFitting_eq_bot_of_center hZ)

end CFSG.Sporadic.HNOddCore
