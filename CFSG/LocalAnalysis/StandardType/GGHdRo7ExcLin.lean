module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyExcWeylAutInner
public import CFSG.LocalAnalysis.StandardType.GGRCAbsIrred
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerF4
public import CFSG.LieType.Chevalley.LangRootArithmeticDet
public import CFSG.Blueprint.Chevalley
public import CFSG.LocalAnalysis.StandardType.GGTableBExcThreeAct
public import CFSG.LieType.Chevalley.RootCommutatorData

open CFSG.StandardType
open CFSG.RankThree.CentralCover
open Multiplicative
open CFSG.LieType.Chevalley hiding cartanFunctional cartanFunctional_apply cartanFunctional_single
open CFSG.Blueprint.Chevalley

public section

local instance instAddCommGroupZModThreeHdRo7ExcLin : AddCommGroup (ZMod 3) := Ring.toAddCommGroup

namespace CFSG.StandardType


set_option maxHeartbeats 400000 in
theorem excWordProd_smul {τ : Tag} (l : List (Fin τ.rank)) (v : Fin τ.rank → ℤ) :
    (CoxeterSystem.wordProd (coxeterSystem τ) l) • v =
      l.foldr (CFSG.Blueprint.Chevalley.reflect τ) v := by
  induction l with
  | nil => simp
  | cons i l ih =>
      rw [CoxeterSystem.wordProd_cons, mul_smul, ih, CFSG.LieType.Chevalley.simple_smul]
      rfl

noncomputable def excW0 (τ : Tag) : WeylGroup τ :=
  (coxeterSystem τ).wordProd ((CFSG.LieType.Chevalley.RootOps.longestWord τ).map τ.idx)

set_option maxHeartbeats 800000 in
theorem excW0_single {τ : Tag} (hτ : τ = Tag.E7 ∨ τ = Tag.E8) (i : Fin τ.rank) :
    excW0 τ • (Pi.single i 1 : Fin τ.rank → ℤ) = -Pi.single i 1 := by
  rcases hτ with rfl | rfl <;> fin_cases i <;>
    (rw [excW0, excWordProd_smul]; decide +kernel)

theorem excW0_smul_eq_neg {τ : Tag} (hτ : τ = Tag.E7 ∨ τ = Tag.E8)
    (β : Fin τ.rank → ℤ) : excW0 τ • β = -β := by
  have hsum : β = ∑ i, β i • (Pi.single i 1 : Fin τ.rank → ℤ) := by
    funext j
    rw [Finset.sum_apply, Finset.sum_eq_single j]
    · simp
    · intro i _ hi
      rw [Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hi), smul_zero]
    · intro hj
      simp at hj
  conv_lhs => rw [hsum]
  rw [Finset.smul_sum]
  simp only [SMulCommClass.smul_comm, excW0_single hτ, smul_neg]
  rw [Finset.sum_neg_distrib, ← hsum]

theorem redMod_neg_local {τ : Tag} {p : ℕ} (v : Fin τ.rank → ℤ) :
    TableBExc.redMod τ p (-v) = -TableBExc.redMod τ p v := by
  funext i
  simp [TableBExc.redMod]

set_option maxHeartbeats 400000 in
theorem torusAct_excW0_eq_neg {τ : Tag} (hτ : τ = Tag.E7 ∨ τ = Tag.E8)
    (x : Fin τ.rank → ZMod 3) :
    TableBExc.torusAct τ 3 (excW0 τ) x = -x := by
  rw [TableBExc.torusAct, excW0_smul_eq_neg hτ (TableBExc.liftMod τ 3 x),
    redMod_neg_local, TableBExc.redMod_liftMod]

@[expose] noncomputable def negOneMulAut (V : Type) [AddCommGroup V] :
    MulAut (Multiplicative V) :=
  AddEquiv.toMultiplicative (AddEquiv.neg V)


theorem negOneMulAut_apply_mul {V : Type} [AddCommGroup V]
    (x : Multiplicative V) :
    negOneMulAut V x = Multiplicative.ofAdd (-Multiplicative.toAdd x) := rfl

theorem torusMulAut_excW0_eq_negOne {τ : Tag} (hτ : τ = Tag.E7 ∨ τ = Tag.E8) :
    ExcWeylOuter.torusMulAut τ 3 (excW0 τ) =
      negOneMulAut (Fin τ.rank → ZMod 3) := by
  ext x
  rw [← ofAdd_toAdd x]
  rw [ExcWeylOuter.torusMulAut_apply, torusAct_excW0_eq_neg hτ (toAdd x)]
  simp [negOneMulAut_apply_mul]


end CFSG.StandardType
