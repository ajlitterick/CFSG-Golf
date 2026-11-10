module

public import CFSG.Milestones.ASVolI.F4Small
public import CFSG.Milestones.ASVolI.F4TISets
public import CFSG.RankThree.PartOne.KC.SymplecticSubfieldOuter
public import CFSG.GH74.KGroups.U33
public import CFSG.Sporadic.Schreier.TitsAutD
import all CFSG.Milestones.ASVolI.F4
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.Monster.B.Fischer.Fi22Order
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.ASVolI.ChF
open CFSG.ComponentClassification.OuterAutomorphisms CFSG.LieType.Chevalley

section F429One


end F429One

section OuterOrders

theorem burnsideF429_card_outer_congr {G H : Type*} [Group G] [Group H] (e : G ≃* H) :
    Nat.card (Outer G) = Nat.card (Outer H) :=
  Nat.card_congr (equivalence e).toEquiv


theorem burnsideF429_card_outer_Un_two {n : ℕ} (hn : n = 4 ∨ n = 5) {H : Type} [Group H]
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ 1) ^ 2)
    (e : H ≃* StatedProj (StatedSU n (2 ^ 1) K)) : Nat.card (Outer H) = 2 := by
  have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 1 K :=
    ⟨Nat.prime_two, le_rfl, by rw [hK]; norm_num⟩
  have hn3 : 3 ≤ n := by omega
  have hq : ¬(n = 3 ∧ 2 ^ 1 = 2) := by omega
  obtain ⟨-, -, -, -, hout, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.unitary_full_diagonal_outer_order hU hn3 hq
  rw [burnsideF429_card_outer_congr
    (e.trans (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSUEquiv hU (by omega)).symm), hout]
  rcases hn with rfl | rfl <;> norm_num

theorem burnsideF429_card_outer_U4two {H : Type} [Group H] (h : IsGenLie H .U4 2 1) :
    Nat.card (Outer H) = 2 := by
  obtain ⟨-, -, K, _, _, hK, ⟨e⟩⟩ := h
  exact burnsideF429_card_outer_Un_two (Or.inl rfl) hK e

theorem burnsideF429_card_outer_U5two {H : Type} [Group H] (h : IsGenLie H .U5 2 1) :
    Nat.card (Outer H) = 2 := by
  obtain ⟨-, -, K, _, _, hK, ⟨e⟩⟩ := h
  exact burnsideF429_card_outer_Un_two (Or.inr rfl) hK e

end OuterOrders

section F429Kinds


end F429Kinds

section L3Top

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
open CFSG.ASVolI.ChF CFSG.ASVolI.ChF.ClassicalRoots


end L3Top

section TopSp

open Matrix CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl CFSG.QuasithinUnique.Setup.X7a
  CFSG.ASVolI.ChF CFSG.ASVolI.ChF.ClassicalRoots


end TopSp

section TopGeneral


end TopGeneral

section G2Two

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Quasithin


end G2Two

section F4Two

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Sporadic.Schreier.Tits CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag


end F4Two

section TopTwo


end TopTwo

section TopF4


end TopF4

section Clause1

open CFSG.ASVolI.ChF


end Clause1

end CFSG.ASVolI
