module

public import CFSG.ClassicalInvolution.Q3.Q3WAE6
public import CFSG.ClassicalInvolution.Q3.Q3WAFive
public import CFSG.ClassicalInvolution.Q3.Q3WARow
public import CFSG.ClassicalInvolution.Q3.Q3WExc

public section

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.Open hiding StatedLieTag
open CFSG.LieType CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.RouteD CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.LieType.CurtisTits CFSG.Timmesfeld
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)

theorem oddLieType_of_model3 {G : Type} [Group G] [IsSimpleGroup G]
    (hnab : ∃ x y : G, x * y ≠ y * x) {t : StatedLieTag} {n : ℕ}
    (hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible t n 3 1)
    (hmodel : CFSG.Blueprint.LieModel (G ⧸ Subgroup.center G) t n 3 1) :
    CFSG.Blueprint.OddLieType G := by
  have hZ : Subgroup.center G = ⊥ := CoreAssembly.center_eq_bot hnab
  let e : G ⧸ Subgroup.center G ≃* G :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  exact ⟨t, n, 3, 1, Nat.prime_three, by norm_num, hadm,
    CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e hmodel⟩

section Chain

variable {G : Type} [Group G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}


end Chain


theorem exists_psi_E6_3 (hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .E6 0 3 1)
    {X : Type} [Group X] (U : Fin 6 → Subgroup X)
    (hcomm : ∀ i j : Fin 6, i ≠ j → ¬ edgeE 6 i j → ¬ edgeE 6 j i → Commutes (U i) (U j))
    (hpair : ∀ i j : Fin 6, edgeE 6 i j →
      ∃ W : Subgroup X, LinearBlockStandardPair (GaloisField 3 1) W (U i) (U j)) :
    ∃ Ψ : (modelUniv .E6 0 3 1 Nat.prime_three).K →* X, Ψ.ker ≤ Subgroup.center _ ∧
      Ψ.range = ⨆ k, U k ∧
      ∀ k, (rankOne (Steinberg.Minuscule.e6Datum (GaloisField 3 1)).rootGroup k).map Ψ = U k := by
  obtain ⟨Ψ', hsurj, hker, -, -, -, hrk⟩ := weakCT3_e6 hadm (F := GaloisField 3 1) card_gf3
    (X := ↥(⨆ k, U k)) (fun k => (U k).subgroupOf (⨆ k, U k)) (iSup_subgroupOf_self U)
    (fun i j hij h1 h2 => chain_commutes_subgroupOf U i j (hcomm i j hij h1 h2))
    (fun i j h => chain_subgroupOf U i j (hpair i j h))
  have key : ∃ Ψ : ↥(Steinberg.Minuscule.e6Data_valid.minGroup (GaloisField 3 1)) →* X,
      Ψ.ker ≤ Subgroup.center _ ∧ Ψ.range = ⨆ k, U k ∧
      ∀ k, (rankOne (Steinberg.Minuscule.e6Datum (GaloisField 3 1)).rootGroup k).map Ψ = U k := by
    refine ⟨(⨆ k, U k).subtype.comp Ψ', ?_, ?_, ?_⟩
    · intro x hx
      exact hker (Subtype.ext (MonoidHom.mem_ker.mp hx))
    · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hsurj, Subgroup.map_top,
        Subgroup.range_subtype]
    · intro k
      rw [← Subgroup.map_map, hrk k, Subgroup.subgroupOf_map_subtype,
        inf_eq_left.mpr (le_iSup U k)]
  exact key


end CFSG.ClassicalInvolution.Q3.Q3W
