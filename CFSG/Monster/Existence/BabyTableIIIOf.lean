module

public import CFSG.Monster.Existence.BabyW2Classes
public import CFSG.Monster.Existence.TwoPoint.ShapeOneHC

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Monster CFSG.Monster.B CFSG.Monster.GMS CFSG.Blueprint MulOpposite

@[expose] noncomputable def babyRep
    (i : ℕ) : NativeSporadic.B := CTIB.iotaEquiv.symm (CTIB.rs i)

@[expose] def babyRepClass (i : ℕ) : Fin 4 :=
  if i = 1 then 0 else if i = 0 then 1 else if i = 3 then 2 else 3

theorem babyTableIII_of_reps
    (h : ∀ i ∈ [1, 0, 5, 3], Nat.card ↥(Subgroup.centralizer ({babyRep i} : Set NativeSporadic.B)) =
      babyCentOrder (babyRepClass i)) :
    BabyTableIII := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hB, -⟩ := CTIB.native_four_involution_classes
  have hcls : ∀ t : NativeSporadic.B, orderOf t = 2 →
      ∃ i ∈ [1, 0, 5, 3], IsConj t (babyRep i) ∧ BabyInv (babyRepClass i) t := by
    intro t ht
    obtain ⟨i, ⟨hi, hc⟩, -⟩ := hB t ht
    exact ⟨i, hi, hc, ht, (natCard_centralizer_eq_of_isConj hc).trans (h i hi)⟩
  refine ⟨fun t ht => ?_, fun k s t hs ht => ?_⟩
  · obtain ⟨i, -, -, hk⟩ := hcls t ht
    exact ⟨_, hk⟩
  · obtain ⟨i, hi, hsi, hki⟩ := hcls s hs.1
    obtain ⟨j, hj, htj, hkj⟩ := hcls t ht.1
    have e1 := BabyInv.unique hki hs
    have e2 := BabyInv.unique hkj ht
    have hij : i = j := by
      have : babyRepClass i = babyRepClass j := e1.trans e2.symm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi hj
      rcases hi with rfl | rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl | rfl <;>
        first | rfl | (exfalso; revert this; decide)
    subst hij
    exact hsi.trans htj.symm

theorem natCard_centralizer_rep_zero :
    Nat.card ↥(Subgroup.centralizer ({babyRep 0} : Set NativeSporadic.B)) = babyCentOrder 1 :=
  (natCard_centralizer_eq_of_isConj
    (isConj_rep_zero_of_rank orderOf_phiB_xBar rank_phiB_xBar_sub_one).symm).trans
    natCard_centralizer_babyW2

theorem orderOf_phiB_uBar :
    orderOf (phiB uBar) = 2 :=
  (@MulEquiv.orderOf_eq _ _ _ Units.instMonoid phiB uBar).trans orderOf_uBar

theorem isConj_rep_one_of_rank
    {X : NativeSporadic.B} (hX : orderOf X = 2)
    (hr : Matrix.rank (X.val.val - 1) = 1860) : IsConj X (babyRep 1) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hB, -, b1, b0, b5, b3⟩ := CTIB.native_four_involution_classes
  obtain ⟨i, ⟨hi, hc⟩, -⟩ := hB X hX
  have hrk := rank_sub_one_of_isConj hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl
  · exact hc
  · rw [hr, b0] at hrk
    exact absurd hrk (by norm_num)
  · rw [hr, b5] at hrk
    exact absurd hrk (by norm_num)
  · rw [hr, b3] at hrk
    exact absurd hrk (by norm_num)

theorem natCard_centralizer_rep_one_of
    (hC : CTIB.CentralizerInput) :
    Nat.card ↥(Subgroup.centralizer ({babyRep 1} : Set NativeSporadic.B)) = babyCentOrder 0 := by
  rw [← natCard_centralizer_eq_of_isConj
    (isConj_rep_one_of_rank orderOf_phiB_uBar rank_phiB_uBar_sub_one)]
  have h1 := Nat.card_congr
    (@centralizerMulEquiv Cbar NativeSporadic.B _ Units.instGroup phiB uBar).toEquiv
  obtain ⟨Ψ⟩ := CTIB.centralizer_equiv_Eam hC
    (CTIB.isConj_labelS_of_rank orderOf_op_uBar rank_betaS_op_uBar)
  rw [← h1, ← Nat.card_congr centOpUBarEquiv.toEquiv, Nat.card_congr Ψ.toEquiv, natCard_Eam,
    CFSG.LieType.Chevalley.C2E6Std.card_stdGroup]
  norm_num [babyCentOrder]

theorem babyTableIII_of
    (hC : CTIB.CentralizerInput)
    (h3 : Nat.card ↥(Subgroup.centralizer ({babyRep 3} : Set NativeSporadic.B)) = babyCentOrder 2)
    (h5 : Nat.card ↥(Subgroup.centralizer ({babyRep 5} : Set NativeSporadic.B)) = babyCentOrder 3) :
    BabyTableIII := by
  refine babyTableIII_of_reps fun i hi => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl
  · exact natCard_centralizer_rep_one_of hC
  · exact natCard_centralizer_rep_zero
  · exact h5
  · exact h3

end CFSG.Monster.Existence
