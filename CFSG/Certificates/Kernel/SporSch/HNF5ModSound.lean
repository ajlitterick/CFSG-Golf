module

public import Certificates.Data.Kernel.SporSch.HNF5Mod
public import Certificates.Data.Kernel.SporSch.HNF5Dig
public import CFSG.Certificates.Kernel.SporSch.HNF5Sound
public import CFSG.Sporadic.HNSchreier.ModuleCheckInputs
import CFSG.Certificates.Kernel.SporSch.HNF5Lane

public section

set_option exponentiation.threshold 2200

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.KS CFSG.Sporadic.He.Native CFSG.Sporadic.HNSchreier.Native

@[expose] noncomputable def vec5 (x : Nat) : Array Nat := Array.ofFn (n := 133) fun j => lane5 x j.val

theorem vec5_get (x : Nat) {j : Nat} (hj : j < 133) : (vec5 x)[j]! = lane5 x j := by
  unfold vec5
  rw [LyM.ofFn_get! _ hj]


theorem vec5_all {x : Nat} (hx : canon5 x = true) : (vec5 x).all (· < 5) = true :=
  F5Lane.all_ofFn_lt fun j => F5Lane.canon5_lane hx j.isLt

theorem mulM5_idR {X : Nat → Nat} (hX : Canon5 X) : mulM 5 133 (rows5 X) (idM 133) = rows5 X := by
  unfold mulM
  conv_rhs => unfold rows5
  refine congrArg Array.ofFn (funext fun i => congrArg Array.ofFn (funext fun k => ?_))
  unfold dot
  rw [LyM.fold_sum]
  have e : ∀ j ∈ Finset.range 133, ((rows5 X)[i.val]!)[j]! * (col 133 (idM 133) k.val)[j]! =
      if j = k.val then lane5 (X i.val) j else 0 := by
    intro j hj
    have hj' := Finset.mem_range.1 hj
    rw [F5Lane.col_get _ hj', F5Lane.idM_get hj' k.isLt, rows5_get _ i.isLt hj']
    split_ifs <;> simp
  rw [Finset.sum_congr rfl e, Finset.sum_ite_eq', ite_eq_left (Finset.mem_range.2 k.isLt),
    Nat.mod_eq_of_lt (F5Lane.canon5_lane (hX i i.isLt) k.isLt)]

theorem invM5_eq {X Y : Nat → Nat} (hX : Canon5 X) (hY : Canon5 Y)
    (h : ∀ i < 133, vm5 Y (X i) = idRow5 i) : invM 5 133 (rows5 X) = rows5 Y := by
  refine (LyM.invM_spec (d := 133) Nat.prime_five (y := fun i j => lane5 (Y i) j)
    (fun i hi j hj => F5Lane.canon5_lane (hY i hi) hj) fun i hi j hj => ?_).trans rfl
  have e := F5Lane.vm5_lane hY (hX i hi) hj
  rw [h i hi, F5Lane.lane5_idRow5] at e
  have e2 := congrArg (fun n : Nat => (n : ZMod 5)) e
  simp only [ZMod.natCast_mod, Nat.cast_sum, Nat.cast_mul] at e2
  rw [Finset.sum_congr rfl fun k hk => by rw [rows5_get _ hi (Finset.mem_range.1 hk)], ← e2]
  by_cases hij : i = j
  · rw [ite_eq_left hij, ite_eq_left hij.symm, Nat.cast_one]
  · rw [ite_eq_right hij, ite_eq_right (Ne.symm hij), Nat.cast_zero]

theorem trans5_sound {T Tt : Nat → Nat} (h : ∀ i < 133, trRow5 T i = Tt i) :
    colsMat 133 (rows5 T) = rows5 Tt ∧ colsMat 133 (rows5 Tt) = rows5 T := by
  constructor
  · unfold colsMat
    conv_rhs => unfold rows5
    refine congrArg Array.ofFn (funext fun i => congrArg Array.ofFn (funext fun t => ?_))
    rw [rows5_get _ t.isLt i.isLt, ← h i i.isLt, F5Lane.lane5_trRow5 _ _ t.isLt]
  · unfold colsMat
    conv_rhs => unfold rows5
    refine congrArg Array.ofFn (funext fun i => congrArg Array.ofFn (funext fun t => ?_))
    rw [rows5_get _ t.isLt i.isLt, ← h t t.isLt, F5Lane.lane5_trRow5 _ _ i.isLt]

theorem mulVec5_sound {M : Nat → Nat} {x : Nat} (hM : Canon5 M) (hx : canon5 x = true) :
    mulVec 5 133 (colsMat 133 (rows5 M)) (vec5 x) = vec5 (vm5 M x) := by
  unfold mulVec
  conv_rhs => unfold vec5
  refine congrArg Array.ofFn (funext fun i => ?_)
  unfold dot
  rw [LyM.fold_sum, F5Lane.vm5_lane hM hx i.isLt]
  refine congrArg (· % 5) (Finset.sum_congr rfl fun j hj => ?_)
  have hj' := Finset.mem_range.1 hj
  rw [F5Lane.colsMat_get _ i.isLt hj', rows5_get _ hj' i.isLt, vec5_get _ hj', Nat.mul_comm]


private theorem xy_cast {X Y : Nat → Nat} (hX : Canon5 X) (hY : Canon5 Y)
    (h : ∀ i < 133, vm5 Y (X i) = idRow5 i) (i : Nat) (hi : i < 133) (j : Nat) (hj : j < 133) :
    ∑ k ∈ Finset.range 133, ((lane5 (X i) k : Nat) : ZMod 5) * ((lane5 (Y k) j : Nat) : ZMod 5) =
      if i = j then 1 else 0 := by
  have e := F5Lane.vm5_lane hY (hX i hi) hj
  rw [h i hi, F5Lane.lane5_idRow5] at e
  have e2 := congrArg (fun n : Nat => (n : ZMod 5)) e
  simp only [ZMod.natCast_mod, Nat.cast_sum, Nat.cast_mul] at e2
  rw [← e2]
  by_cases hij : i = j
  · rw [ite_eq_left hij, ite_eq_left hij.symm, Nat.cast_one]
  · rw [ite_eq_right hij, ite_eq_right (Ne.symm hij), Nat.cast_zero]

private theorem comm_cast {d : Nat} {x y : Nat → Nat → ZMod 5}
    (h : ∀ i < d, ∀ j < d, ∑ k ∈ Finset.range d, x i k * y k j = if i = j then 1 else 0) :
    ∀ i < d, ∀ j < d, ∑ k ∈ Finset.range d, y i k * x k j = if i = j then 1 else 0 := by
  let Mx : Matrix (Fin d) (Fin d) (ZMod 5) := fun a b => x a.val b.val
  let My : Matrix (Fin d) (Fin d) (ZMod 5) := fun a b => y a.val b.val
  have h1 : Mx * My = 1 := by
    ext a b
    rw [Matrix.mul_apply, Fin.sum_univ_eq_sum_range (fun k => x a.val k * y k b.val),
      h a.val a.isLt b.val b.isLt, Matrix.one_apply]
    simp [Fin.ext_iff]
  have h2 : My * Mx = 1 := mul_eq_one_comm.1 h1
  intro i hi j hj
  have e := congrFun (congrFun h2 ⟨i, hi⟩) ⟨j, hj⟩
  rw [Matrix.mul_apply, Fin.sum_univ_eq_sum_range (fun k => y i k * x k j), Matrix.one_apply] at e
  rw [e]
  simp [Fin.ext_iff]

private theorem mulM_idM_of {p d : Nat} (hp : 1 < p) {P Q : Array (Array Nat)}
    (h : ∀ i < d, ∀ k < d, ∑ j ∈ Finset.range d,
      (((P[i]!)[j]! : Nat) : ZMod p) * (((Q[j]!)[k]! : Nat) : ZMod p) = if i = k then 1 else 0) :
    mulM p d P Q = idM d := by
  unfold mulM idM
  refine congrArg Array.ofFn (funext fun i => congrArg Array.ofFn (funext fun k => ?_))
  unfold dot
  rw [LyM.fold_sum]
  have hd : (if i.val = k.val then 1 else 0) < p := by split_ifs <;> omega
  refine (LyM.mod_of_cast hd ?_).symm
  rw [Nat.cast_sum, Finset.sum_congr rfl fun j hj => by
    rw [F5Lane.col_get _ (Finset.mem_range.1 hj), Nat.cast_mul], h i i.isLt k k.isLt]
  split_ifs <;> simp

theorem inv5_sound {X Y : Nat → Nat} (hX : Canon5 X) (hY : Canon5 Y)
    (h : ∀ i < 133, vm5 Y (X i) = idRow5 i) :
    (mulM 5 133 (rows5 X) (invM 5 133 (rows5 X)) == idM 133) = true ∧
      (mulM 5 133 (colsMat 133 (rows5 X)) (invM 5 133 (colsMat 133 (rows5 X))) == idM 133) =
        true := by
  constructor
  · rw [invM5_eq hX hY h, mulM5_sound hX hY h, rows5_eq_idM fun i _ => rfl]
    exact beq_self_eq_true _
  · have hYX := comm_cast (d := 133) (x := fun i k => ((lane5 (X i) k : Nat) : ZMod 5))
      (y := fun k j => ((lane5 (Y k) j : Nat) : ZMod 5)) (xy_cast hX hY h)
    have hT : ∀ i < 133, ∀ k < 133, ∑ j ∈ Finset.range 133,
        ((lane5 (X j) i : Nat) : ZMod 5) * ((lane5 (Y k) j : Nat) : ZMod 5) =
          if i = k then 1 else 0 := by
      intro i hi k hk
      rw [Finset.sum_congr rfl fun j _ => mul_comm _ _, hYX k hk i hi]
      by_cases hik : i = k
      · rw [ite_eq_left hik, ite_eq_left hik.symm]
      · rw [ite_eq_right hik, ite_eq_right (Ne.symm hik)]
    have hP : ∀ i < 133, ∀ j < 133, ((colsMat 133 (rows5 X))[i]!)[j]! = lane5 (X j) i :=
      fun i hi j hj => by rw [F5Lane.colsMat_get _ hi hj, rows5_get _ hj hi]
    have hinv := LyM.invM_spec (d := 133) Nat.prime_five (X := colsMat 133 (rows5 X))
      (y := fun i j => lane5 (Y j) i) (fun i _ j hj => F5Lane.canon5_lane (hY j hj) (by omega))
      fun i hi j hj => by
        rw [← hT i hi j hj]
        exact Finset.sum_congr rfl fun k hk => by rw [hP i hi k (Finset.mem_range.1 hk)]
    rw [hinv, mulM_idM_of (by norm_num) fun i hi k hk => ?_]
    · exact beq_self_eq_true _
    · rw [← hT i hi k hk]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hj' := Finset.mem_range.1 hj
      rw [hP i hi j hj', LyM.ofFn_get! _ hj', LyM.ofFn_get! _ hk]


end CFSG.KS.SporSch

end
